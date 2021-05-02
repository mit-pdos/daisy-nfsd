include "inode_fs.dfy"
include "indirect/ind_block.dfy"
include "indirect/pos.dfy"

module IndFs
{
  import opened Std
  import opened Machine
  import opened ByteSlice
  import opened FsKinds
  import opened JrnlTypes
  import opened JrnlSpec
  import opened InodeFs
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
    const fs: InodeFilesys<Pos>
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
      requires |blks| == 12
      requires pos_dom(to_blkno)
    {
      forall k: uint64 | k < 12 ::
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

    lemma inode_pos_at(ino: Ino, i: MemInode)
      requires ValidIno(ino, i)
      ensures inode_pos_match(ino, i.blks, to_blkno)
    {
      reveal ValidInodes();
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

    lemma valid_parent_at(pos: Pos)
      requires pos.ilevel > 0
      requires ValidBasics() && ValidIndirect()
      ensures valid_parent(pos)
    {
      reveal ValidIndirect();
    }

    lemma parent_zero(pos: Pos)
      requires pos.ilevel > 0
      requires ValidBasics() && ValidIndirect()
      requires to_blkno[pos.parent()] == 0
      ensures to_blkno[pos] == 0
    {
      valid_parent_at(pos);
      IndBlocks.to_blknos_zero();
    }

    predicate {:opaque} ValidData()
      reads Repr
      requires ValidBasics()
    {
      forall pos:Pos | pos.data? ::
        data[pos] == zero_lookup(fs.data_block, to_blkno[pos])
    }

    lemma data_zero(pos: Pos)
      requires ValidBasics() && ValidData()
      requires to_blkno[pos] == 0
      requires pos.data?
      ensures data[pos] == block0
    {
      reveal ValidData();
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
      ensures data == imap pos: Pos {:trigger pos.idx.data?()} | pos.idx.data? ():: block0
      ensures metadata == map ino: Ino {:trigger} :: Inode.Meta.zero
    {
      this.fs := new InodeFilesys.Init(d);
      this.to_blkno := imap pos: Pos {:trigger} :: 0 as Blkno;
      this.data := imap pos: Pos | pos.idx.data?() :: block0;
      this.metadata := map ino: Ino {:trigger} :: Inode.Meta.zero;
      new;
      assert ValidBasics() by { reveal fsValid(); }
      IndBlocks.to_blknos_zero();
      assert ValidPos() by { reveal ValidPos(); }
      reveal ValidInodes();
      reveal ValidIndirect();
      reveal ValidMetadata();
      reveal ValidData();
    }

    constructor Recover(jrnl_: Jrnl, ghost fs: IndFilesys)
      modifies {}
      requires fs.ValidQ()
      requires same_jrnl(jrnl_, fs.fs.jrnl)
      ensures this.to_blkno == fs.to_blkno
      ensures this.data == fs.data
      ensures this.metadata == fs.metadata
      ensures this.fs.jrnl == jrnl_
      ensures ValidQ()
      ensures fresh(Repr - {jrnl_})
    {
      this.fs := new InodeFilesys.Recover(jrnl_, fs.fs);

      this.to_blkno := fs.to_blkno;
      this.data := fs.data;
      this.metadata := fs.metadata;

      new;
      assert ValidBasics() by { reveal fsValid(); }
      assert ValidPos() by { reveal ValidPos(); }
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

    twostate lemma ValidPos_dealloc_one(bn: Blkno, pos: Pos)
      requires old(ValidBasics()) && ValidBasics()
      requires blkno_ok(bn)
      requires old(blkno_pos(bn).Some?) && old(to_blkno[pos] == bn)
      requires fs.block_used == old(fs.block_used[bn:=None])
      requires to_blkno == old(to_blkno[pos:=0 as Blkno])
      requires old(ValidPos())
      ensures ValidPos()
    {
      reveal ValidPos();
    }

    twostate lemma ValidInodes_change_one(pos: Pos, i': MemInode, bn:Blkno)
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
    method allocateRootMetadata(txn: Txn, pos: Pos, i: MemInode)
      returns (ok: bool, bn: Blkno)
      modifies Repr, i.Repr
      requires has_jrnl(txn)
      requires ValidIno(pos.ino, i) ensures ValidIno(pos.ino, i)
      requires  pos.ilevel == 0 && i.blks[pos.idx.k] == 0
      ensures ok ==> bn != 0 && blkno_ok(bn) && bn == to_blkno[pos]
      ensures !ok ==> bn == 0 && to_blkno[pos] == 0
      ensures state_unchanged()
    {
      var idx := pos.idx;
      assert to_blkno[pos] == 0 by {
        reveal ValidInodes();
      }
      ok, bn := fs.allocateTo(txn, pos);
      if !ok {
        Valid_unchanged();
        bn := 0;
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

    // Allocate an indirect block for an intermediate position in place of a
    // zero block. Does not affect the user state but makes it possible to
    // allocate data blocks and store them underneath this indirect block.
    method {:timeLimitMultiplier 2} allocateIndirectMetadata(txn: Txn,
      pos: Pos, ibn: Blkno, pblock: Bytes)
      returns (ok: bool, bn: Blkno)
      modifies Repr, pblock
      requires has_jrnl(txn)
      requires Valid() ensures Valid()
      requires pos.ilevel > 0 && to_blkno[pos] == 0
      requires ibn == to_blkno[pos.parent()]
      requires ibn != 0
      requires pblock.data == zero_lookup(fs.data_block, ibn)
      ensures to_blkno[pos] == bn
      ensures ok == (bn != 0)
      ensures fs.cur_inode == old(fs.cur_inode)
      ensures fs.inodes == old(fs.inodes)
      ensures state_unchanged()
    {
      assert IndBlocks.to_blknos(block0) == IndBlocks.IndBlknos.zero by {
        IndBlocks.to_blknos_zero();
      }
      ok, bn := fs.allocateTo(txn, pos);
      if !ok {
        bn := 0;
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
      IndBlocks.modify_one(pblock, child.j, bn);
      fs.writeDataBlock(txn, ibn, pblock);
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
      ensures bn == to_blkno[pos]
      ensures ok == (bn != 0)
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
      if !ok {
        bn := 0;
        IndBlocks.to_blknos_zero();
        reveal ValidIndirect();
        return;
      }
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
        IndBlocks.to_blknos_zero();
        reveal ValidIndirect();
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
      ensures i.attrs == metadata[ino].attrs
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

    method write(txn: Txn, pos: Pos, i: MemInode, blk: Bytes)
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
      requires off < 8
      ensures data == old(data[Pos.from_flat(ino, off) := block0])
      ensures metadata == old(metadata)
    {
      ghost var pos := Pos.from_flat(ino, off);
      assert pos.idx.off == IndOff.direct;
      assert pos.data?;
      var bn: Blkno := i.get_blk(off);
      if bn == 0 {
        // already done
        inode_pos_at(ino, i);
        data_zero(pos);
        return;
      }
      inode_pos_at(ino, i);
      assert blkno_pos(bn).Some? by {
        reveal ValidPos();
      }
      fs.free(txn, bn);
      i.set_blk(off, 0);
      fs.writeInode(ino, i);
      data := old(data[pos := block0]);
      to_blkno := to_blkno[pos := 0 as Blkno];
      assert ValidMetadata() by { reveal ValidMetadata(); }
      assert ValidIndirect() by { reveal ValidIndirect(); }

      assert ValidPos() by {
        reveal ValidPos();
        reveal ValidInodes();
      }
      ValidInodes_change_one(pos, i, 0 as Blkno);
      assert ValidData() by {
        reveal ValidData();
      }
    }

    // TODO: this proof is very slow, but it does work!
    method {:timeLimitMultiplier 2} zeroOutIndirect(txn: Txn, pos: Pos, ghost ino: Ino, i: MemInode)
      modifies Repr, i.Repr
      requires has_jrnl(txn)
      requires ino == pos.ino
      requires ValidIno(ino, i) ensures ValidIno(ino, i)
      requires pos.ilevel > 0 // indirect
      requires pos.data?      // last level
      ensures data == old(data[pos := block0])
      ensures metadata == old(metadata)
    {
      var _, ibn := resolveMetadata(txn, pos.parent(), i);
      if ibn == 0 {
        parent_zero(pos);
        data_zero(pos);
        return;
      }
      valid_parent_at(pos);
      var parent: Pos := pos.parent();
      var child: IndOff := pos.child();
      var ib: Bytes := fs.getDataBlock(txn, ibn);
      var child_bn := IndBlocks.decode_one(ib, child.j);
      if child_bn == 0 {
        data_zero(pos);
        return;
      }
      label pre_state:
      assert blkno_pos(child_bn).Some? by {
        reveal ValidPos();
      }
      fs.free(txn, child_bn);
      IndBlocks.modify_one(ib, child.j, 0);
      fs.writeDataBlock(txn, ibn, ib);
      data := data[pos := block0];
      to_blkno := to_blkno[pos := 0 as Blkno];
      assert ValidBasics();
      assert ValidPos() by {
        ValidPos_dealloc_one@pre_state(child_bn, pos);
      }
      // up to here proof takes 8s
      assert ValidData() by {
        reveal ValidPos();
        reveal ValidData();
      }
      assert valid_parent(pos) by {
        IndBlocks.to_blknos_zero();
      }
      assert ValidMetadata() by { reveal ValidMetadata(); }
      assert ValidInodes() by { reveal ValidInodes(); }
      // up to here 12s
      assert ValidIndirect() by {
        reveal ValidIndirect();
        var pos0 := pos;
        forall pos: Pos | pos.ilevel > 0
          ensures valid_parent(pos)
        {
          if pos == pos0  {}
          else {
            if pos.parent() == pos0 {
              reveal ValidPos();
            } else {
              reveal ValidPos();
            }
          }
        }
      }
      // up to here is 26s, about same with postcondition
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
      i.set_sz(meta.sz);
      i.set_attrs(meta.attrs);
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
      modifies Repr, i.bs
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
