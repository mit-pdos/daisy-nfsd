include "fs.dfy"
include "ind_block.dfy"
include "pos.dfy"

module IndFs
{
  import opened Std
  import opened Machine
  import opened ByteSlice
  import opened FsKinds
  import opened JrnlTypes
  import opened JrnlSpec
  import opened Fs
  import opened Marshal
  import C = Collections

  import IndBlocks
  import opened IndirectPos
  import opened MemInodes

  predicate pos_dom<T>(m: imap<Pos, T>)
  {
    forall p:Pos :: p in m
  }

  predicate data_dom<T>(m: imap<Pos, T>)
  {
    forall pos: Pos | pos.data? :: pos in m
  }

  lemma inode_size_ok()
    ensures 4096*config.total == Inode.MAX_SZ
  {
    config_properties();
  }

  class IndFilesys
  {
    // filesys contains a mapping from allocated Blkno's to poss
    const fs: Filesys<Pos>
    // this is a complete map; every position in every inode has a value, but
    // it might be a zero block encoded efficiently via 0's.
    ghost var to_blkno: imap<Pos, Blkno>

    // public abstract state

    // only maps pos where pos.data? (this hides when other blocks change but
    // exposes newly-allocated data blocks)
    ghost var data: imap<Pos, Block>
    // bubbles up inode sizes
    ghost var metadata: map<Ino, Inode.Meta>

    function blkno_pos(bn: Blkno): Option<Pos>
      reads fs.Repr
      requires blkno_ok(bn)
      requires fsValid()
    {
      reveal fsValid();
      fs.block_used[bn]
    }

    predicate has_jrnl(txn: Txn)
      reads fs
    {
      txn.jrnl == fs.jrnl
    }

    ghost const Repr: set<object> := {this} + fs.Repr

    predicate ValidBlknos()
      reads this
    {
      && pos_dom(to_blkno)
      && (forall pos:Pos :: blkno_ok(to_blkno[pos]))
    }

    predicate {:opaque} fsValid()
      reads fs.Repr
    {
      fs.Valid()
    }

    predicate ValidBasics()
      reads Repr
    {
      reveal fsValid();
      && fsValid()
      && ino_dom(metadata)
      && data_dom(data)
      && ValidBlknos()
      && fs.block_used[0].None?
    }

    predicate {:opaque} ValidPos()
      reads Repr
      requires ValidBasics()
    {
      reveal fsValid();
      && (forall bn:Blkno | bn != 0 && blkno_ok(bn) ::
          blkno_pos(bn).Some? ==> to_blkno[blkno_pos(bn).x] == bn)
      && (forall pos:Pos ::
          var bn := to_blkno[pos];
          && blkno_ok(bn)
          && (bn != 0 ==> blkno_pos(bn) == Some(pos)))
    }

    lemma blkno_unused(bn: Blkno)
      requires ValidBasics() && ValidPos()
      requires blkno_ok(bn) && bn != 0 && blkno_pos(bn).None?
      ensures forall pos: Pos :: to_blkno[pos] != bn
    {
      reveal ValidPos();
    }

    predicate {:opaque} ValidMetadata()
      reads Repr
      requires ValidBasics()
    {
      forall ino: Ino ::
        && fs.inodes[ino].meta == metadata[ino]
        && metadata[ino].sz as nat <= Inode.MAX_SZ
    }

    static predicate inode_pos_match(ino: Ino, blks: seq<Blkno>, to_blkno: imap<Pos, Blkno>)
      requires |blks| == 14
      requires pos_dom(to_blkno)
    {
      forall k: uint64 | k < 14 ::
        var bn := blks[k];
        && blkno_ok(bn)
        && to_blkno[Pos(ino, Idx.from_inode(k))] == bn
        // && (bn != 0 ==> blkno_pos(bn) == Some(MkPos(ino, Idx.from_inode(k))))
    }

    predicate {:opaque} ValidInodes()
      reads Repr
      requires ValidBasics()
    {
      forall ino:Ino :: inode_pos_match(ino, fs.inodes[ino].blks, to_blkno)
    }

    predicate valid_parent(pos: Pos)
      reads Repr
      requires pos.ilevel > 0
      requires ValidBasics()
    {
      var parent := to_blkno[pos.parent()];
      var blknos := IndBlocks.to_blknos(zero_lookup(fs.data_block, parent));
      var j := pos.child().j;
      var bn := to_blkno[pos];
      blknos.s[j] == bn
    }

    predicate {:opaque} ValidIndirect()
      reads Repr
      requires ValidBasics()
    {
      forall pos: Pos | pos.ilevel > 0 :: valid_parent(pos)
    }

    predicate {:opaque} ValidData()
      reads Repr
      requires ValidBasics()
    {
      forall pos:Pos | pos.data? ::
        data[pos] == zero_lookup(fs.data_block, to_blkno[pos])
    }

    predicate Valid()
      reads this.Repr
    {
      && ValidBasics()
      && ValidBlknos()
      && ValidPos()
      && ValidInodes()
      && ValidMetadata()
      && ValidIndirect()
      && ValidData()
    }

    predicate ValidIno(ino: Ino, i: MemInode)
      reads this.Repr, i.Repr
    {
      && Valid()
      && i.Valid()
      && fs.is_cur_inode(ino, i.val())
    }

    predicate ValidQ()
      reads Repr
    {
      && Valid()
      && fs.quiescent()
    }

    constructor Init(d: Disk)
      ensures ValidQ()
      ensures fresh(Repr)
      ensures data == imap pos: Pos | pos.idx.data? :: block0
      ensures metadata == map ino: Ino {:trigger} :: Inode.Meta(0, Inode.InvalidType)
    {
      this.fs := new Filesys.Init(d);
      this.to_blkno := imap pos: Pos {:trigger} :: 0 as Blkno;
      this.data := imap pos: Pos | pos.idx.data? :: block0;
      this.metadata := map ino: Ino {:trigger} :: Inode.Meta(0, Inode.InvalidType);
      new;
      assert ValidBasics() by { reveal fsValid(); }
      IndBlocks.to_blknos_zero();
      reveal ValidPos();
      reveal ValidInodes();
      reveal ValidIndirect();
      reveal ValidMetadata();
      reveal ValidData();
    }

    // private read
    method read_(txn: Txn, pos: Pos, i: MemInode) returns (b: Bytes)
      decreases pos.ilevel
      requires has_jrnl(txn)
      requires ValidIno(pos.ino, i)
      ensures is_block(b.data)
      ensures b.data == zero_lookup(fs.data_block, to_blkno[pos])
      ensures fresh(b)
    {
      reveal ValidInodes();
      var idx := pos.idx;
      if pos.ilevel == 0 {
        reveal ValidPos();
        assert idx.off == IndOff.direct;
        var bn := i.get_blk(idx.k);
        if bn == 0 {
          b := NewBytes(4096);
          return;
        }
        b := fs.getDataBlock(txn, bn);
        return;
      }
      // recurse
      var parent: Pos := pos.parent();
      var child: IndOff := pos.child();
      var ib: Bytes := this.read_(txn, parent, i);
      var child_bn := IndBlocks.decode_one(ib, child.j);
      reveal ValidIndirect();
      b := fs.getDataBlock(txn, child_bn);
      // NOTE(tej): I can't believe this worked the first time
      reveal ValidData();
    }

    twostate lemma ValidPos_alloc_one(bn: Blkno, pos: Pos)
      requires old(ValidBasics()) && ValidBasics()
      requires blkno_ok(bn)
      requires old(blkno_pos(bn).None?) && old(to_blkno[pos] == 0)
      requires fs.block_used == old(fs.block_used[bn:=Some(pos)])
      requires to_blkno == old(to_blkno[pos:=bn])
      requires old(ValidPos())
      ensures ValidPos()
    {
      reveal ValidPos();
    }

    twostate lemma {:timeLimitMultiplier 2} ValidInodes_change_one(pos: Pos, i': MemInode, bn:Blkno)
      requires old(ValidBasics()) && ValidBasics()
      requires pos.ilevel == 0
      requires to_blkno == old(to_blkno[pos:=bn])
      requires i'.Valid()
      requires fs.inodes == old(fs.inodes)[pos.ino:=i'.val()]
      requires blkno_ok(bn)
      requires i'.val() == old(var i := fs.inodes[pos.ino]; i.(blks:=i.blks[pos.idx.k := bn]))
      requires old(ValidInodes())
      ensures ValidInodes()
    {
      reveal ValidInodes();
      assert inode_pos_match(pos.ino, i'.blks, to_blkno);
    }

    twostate predicate state_unchanged()
      reads this, fs
    {
      && data == old(data)
      && metadata == old(metadata)
    }

    twostate lemma Valid_unchanged()
      requires old(Valid())
      requires
          && fs.Valid()
          && fs.data_block == old(fs.data_block)
          && fs.inodes == old(fs.inodes)
          && fs.block_used == old(fs.block_used)
          && data == old(data)
          && metadata == old(metadata)
          && to_blkno == old(to_blkno)
      ensures Valid()
    {
      reveal ValidPos();
      reveal ValidInodes();
      reveal ValidData();
      reveal ValidIndirect();
      reveal ValidMetadata();
    }

    // private
    method {:timeLimitMultiplier 2} allocateRootMetadata(txn: Txn, pos: Pos, i: MemInode)
      returns (ok: bool, bn: Blkno)
      modifies Repr, i.Repr
      requires has_jrnl(txn)
      requires ValidIno(pos.ino, i) ensures ValidIno(pos.ino, i)
      requires  pos.ilevel == 0 && i.blks[pos.idx.k] == 0
      ensures ok ==> bn != 0 && blkno_ok(bn) && bn == to_blkno[pos]
      ensures state_unchanged()
    {
      var idx := pos.idx;
      assert to_blkno[pos] == 0 by {
        reveal ValidInodes();
      }
      ok, bn := fs.allocateTo(txn, pos);
      if !ok {
        Valid_unchanged();
        return;
      }

      i.set_blk(idx.k, bn);
      fs.writeInode(pos.ino, i);

      to_blkno := to_blkno[pos:=bn];
      var zeroblk := NewBytes(4096);
      fs.writeDataBlock(txn, bn, zeroblk);

      assert ValidPos() by {
        ValidPos_alloc_one(bn, pos);
      }
      assert ValidInodes() by {
        ValidInodes_change_one(pos, i, bn);
      }
      assert ValidMetadata() by { reveal ValidMetadata(); }
      assert ValidIndirect() && ValidData() by {
        reveal ValidPos();
        reveal ValidIndirect();
        reveal ValidData();
      }
    }

    method {:timeLimitMultiplier 2} allocateIndirectMetadata(txn: Txn, pos: Pos, ibn: Blkno, pblock: Bytes)
      returns (ok: bool, bn: Blkno)
      modifies Repr, pblock
      requires has_jrnl(txn)
      requires Valid() ensures Valid()
      requires pos.ilevel > 0 &&  to_blkno[pos] == 0
      requires ibn == to_blkno[pos.parent()]
      requires ibn != 0
      requires pblock.data == zero_lookup(fs.data_block, ibn)
      ensures ok ==> bn != 0 && bn == to_blkno[pos]
      ensures fs.cur_inode == old(fs.cur_inode)
      ensures fs.inodes == old(fs.inodes)
      ensures state_unchanged()
    {
      assert IndBlocks.to_blknos(block0) == IndBlocks.IndBlknos.zero by {
        IndBlocks.to_blknos_zero();
      }
      ok, bn := fs.allocateTo(txn, pos);
      if !ok {
        Valid_unchanged();
        return;
      }
      to_blkno := to_blkno[pos := bn];
      // NOTE(tej): I was formerly only doing this for data blocks, but I think
      // it might be necessary for metadata blocks to preserve that children are
      // still zeros (I was unable to prove ValidIndirect() without this for the
      // special case of pos where pos.parent() == pos0). In that case
      // verification caught a bug! (Albeit one only with holes but still.)
      var zeroblock := NewBytes(4096);
      fs.writeDataBlock(txn, bn, zeroblock);

      var child := pos.child();
      var pblock' := IndBlocks.modify_one(pblock, child.j, bn);
      fs.writeDataBlock(txn, ibn, pblock');
      assert valid_parent(pos);

      assert ValidPos() by {
        ValidPos_alloc_one(bn, pos);
      }

      assert ValidInodes() by {
        reveal ValidPos();
        reveal ValidInodes();
      }

      assert ValidData() by {
        reveal ValidPos();
        reveal ValidData();
      }

      assert ValidMetadata() by { reveal ValidMetadata(); }

      assert ValidIndirect() by {
        reveal ValidIndirect();
        // reveal ValidPos();
        var pos0 := pos;
        forall pos: Pos | pos.ilevel > 0
          ensures valid_parent(pos)
        {
          if pos == pos0  {}
          else {
            if pos.parent() == pos0 {
              IndBlocks.to_blknos_zero();
              reveal ValidPos();
            } else {
              reveal ValidPos();
            }
          }
        }
      }
    }

    // private
    method resolveMetadata(txn: Txn, pos: Pos, i: MemInode) returns (ok: bool, bn: Blkno)
      decreases pos.ilevel
      modifies Repr, i.Repr
      requires has_jrnl(txn)
      requires ValidIno(pos.ino, i) ensures ValidIno(pos.ino, i)
      ensures ok ==> bn != 0 && bn == to_blkno[pos]
      ensures state_unchanged()
    {
      reveal ValidInodes();
      var idx := pos.idx;
      if pos.ilevel == 0 {
        assert idx.off == IndOff.direct;
        bn := i.get_blk(idx.k);
        if bn != 0 {
          // we haven't actually written anything, just resolved existing metadata
          ok := true;
          return;
        }
        assert bn == 0;
        // need to allocate a top-level indirect block
        ok, bn := allocateRootMetadata(txn, pos, i);
        return;
      }
      // recurse
      var parent: Pos := pos.parent();
      var child: IndOff := pos.child();
      var ibn;
      ok, ibn := this.resolveMetadata(txn, parent, i);
      if !ok { return; }
      // now we have somewhere to store the reference to this block, but might
      // need to allocate into the parent
      var pblock := fs.getDataBlock(txn, ibn);
      bn := IndBlocks.decode_one(pblock, child.j);
      assert bn == to_blkno[pos] by {
        reveal ValidIndirect();
      }
      assert ValidIno(pos.ino, i);
      assert state_unchanged();
      if bn != 0 {
        return;
      }

      ok, bn := allocateIndirectMetadata(txn, pos, ibn, pblock);
      assert ValidIno(pos.ino, i);
      if !ok {
        return;
      }
    }

    // public
    //
    // data version of more general read_ spec
    method read(txn: Txn, pos: Pos, i: MemInode) returns (b: Bytes)
      requires has_jrnl(txn)
      requires ValidIno(pos.ino, i)
      requires pos.data?
      ensures pos in data && b.data == data[pos]
      ensures fresh(b)
    {
      b := this.read_(txn, pos, i);
      reveal ValidData();
    }

    // caller can extract size themselves
    lemma inode_metadata(ino: Ino, i: MemInode)
      requires ValidIno(ino, i)
      ensures i.sz == metadata[ino].sz
      ensures i.ty == metadata[ino].ty
    {
      reveal ValidMetadata();
      assert i.val().meta == metadata[ino];
    }

    lemma metadata_bound(ino: Ino)
      requires Valid()
      ensures metadata[ino].sz as nat <= Inode.MAX_SZ
    {
      reveal ValidMetadata();
    }

    method {:timeLimitMultiplier 2} write(txn: Txn, pos: Pos, i: MemInode, blk: Bytes)
      returns (ok: bool)
      modifies Repr, i.Repr
      requires has_jrnl(txn)
      requires ValidIno(pos.ino, i) ensures ValidIno(pos.ino, i)
      requires pos.data?
      requires is_block(blk.data)
      ensures ok ==> data == old(data[pos := blk.data])
      ensures !ok ==> data == old(data)
      ensures metadata == old(metadata)
    {
      var i': MemInode := i;
      var idx := pos.idx;
      var bn;
      ok, bn := this.resolveMetadata(txn, pos, i');
      if !ok {
         return;
      }
      assert ValidIno(pos.ino, i');

      fs.writeDataBlock(txn, bn, blk);
      data := data[pos := blk.data];

      assert ValidPos() by {
        reveal ValidPos();
      }
      assert ValidInodes() by {
        reveal ValidPos();
        reveal ValidInodes();
      }
      assert ValidData() by {
        reveal ValidPos();
        reveal ValidData();
      }
      assert ValidMetadata() by { reveal ValidMetadata(); }
      assert ValidIndirect() by {
        reveal ValidPos();
        reveal ValidIndirect();
      }
    }

    method zeroOut(txn: Txn, off: uint64, ghost ino: Ino, i: MemInode)
      modifies Repr, i.Repr
      requires has_jrnl(txn)
      requires ValidIno(ino, i) ensures ValidIno(ino, i)
      // serious limitation for now to only zero the direct blocks (indirect
      // blocks are also not too bad, but eventually we'll run the risk of
      // overflowing a transaction and it'll be necessary to split, which is
      // complicated)
      requires off < 10
      ensures data == old(data[Pos.from_flat(ino, off) := block0])
      ensures metadata == old(metadata)
    {
      var i': MemInode := i;
      ghost var pos := Pos.from_flat(ino, off);
      assert pos.idx.off == IndOff.direct;
      assert pos.data?;
      var bn: Blkno := i'.get_blk(off);
      if bn == 0 {
        // already done, need to reveal some stuff to prove that
        reveal ValidInodes();
        reveal ValidData();
        return;
      }
      assert inode_pos_match(ino, i.blks, to_blkno) by {
        reveal ValidInodes();
      }
      assert blkno_pos(bn).Some? by {
        reveal ValidPos();
      }
      fs.free(txn, bn);
      i'.set_blk(off, 0);
      fs.writeInode(ino, i');
      data := old(data[pos := block0]);
      to_blkno := to_blkno[pos := 0 as Blkno];
      assert ValidMetadata() by { reveal ValidMetadata(); }
      assert ValidIndirect() by { reveal ValidIndirect(); }

      assert ValidPos() by {
        reveal ValidPos();
        reveal ValidInodes();
      }
      ValidInodes_change_one(pos, i', 0 as Blkno);
      assert ValidData() by {
        reveal ValidData();
      }
    }

    // public
    method startInode(txn: Txn, ino: Ino)
      returns (i: MemInode)
      modifies fs
      requires has_jrnl(txn)
      requires ValidQ()
      ensures ValidIno(ino, i)
      ensures fs.cur_inode == Some((ino, i.val()))
      ensures state_unchanged()
      ensures fresh(i.Repr)
    {
      i := fs.getInode(txn, ino);
      fs.startInode(ino, i.val());
      Valid_unchanged();
    }

    // public
    method writeInodeMeta(ghost ino: Ino, i: MemInode, meta: Inode.Meta)
      modifies Repr, i
      requires ValidIno(ino, i)
      requires meta.sz <= Inode.MAX_SZ_u64
      ensures ValidIno(ino, i)
      ensures data == old(data)
      ensures metadata == old(metadata[ino := meta])
    {
      reveal fsValid();
      i.set_ty(meta.ty);
      i.set_sz(meta.sz);
      fs.writeInode(ino, i);
      metadata := metadata[ino := meta];
      assert ValidBasics();
      assert ValidMetadata() by { reveal ValidMetadata(); }
      assert ValidInodes() by { reveal ValidInodes(); }
      assert ValidPos() by { reveal ValidPos(); }
      assert ValidIndirect() by { reveal ValidIndirect(); }
      assert ValidData() by { reveal ValidData(); }
    }

    // public
    method finishInode(txn: Txn, ino: Ino, i: MemInode)
      modifies Repr, i.Repr
      requires ValidIno(ino, i)
      requires has_jrnl(txn)
      ensures ValidQ()
      ensures state_unchanged()
    {
      fs.finishInode(txn, ino, i);
      Valid_unchanged();
    }

    // public
    ghost method finishInodeReadonly(ino: Ino, i: MemInode)
      modifies fs
      requires ValidIno(ino, i)
      requires fs.cur_inode == Some((ino, i.val()))
      ensures ValidQ()
      ensures state_unchanged()
    {
      fs.finishInodeReadonly(ino, i.val());
      Valid_unchanged();
    }

  }

}
