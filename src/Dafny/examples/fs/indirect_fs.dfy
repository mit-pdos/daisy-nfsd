include "fs.dfy"
include "ind_block.dfy"
include "pos.dfy"

module IndFs
{
  import opened Machine
  import opened ByteSlice
  import opened FsKinds
  import opened JrnlTypes
  import opened JrnlSpec
  import opened Fs
  import opened Marshal
  import IndBlocks
  import opened IndirectPos
  import C = Collections

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
  {}

  class IndFilesys<InodeAllocState(!new)>
  {
    // filesys contains a mapping from allocated Blkno's to poss
    const fs: Filesys<Pos, InodeAllocState>
    // this is a complete map; every position in every inode has a value, but
    // it might be a zero block encoded efficiently via 0's.
    ghost var to_blkno: imap<Pos, Blkno>

    // public abstract state

    // only maps pos where pos.data? (this hides when other blocks change but
    // exposes newly-allocated data blocks)
    ghost var data: imap<Pos, Block>
    // bubbles up inode sizes
    ghost var metadata: map<Ino, nat>

    function inode_owner(): (m:map<Ino, Option<InodeAllocState>>)
      requires fsValid()
      reads fs.Repr
      ensures ino_dom(m)
    {
      reveal fsValid();
      fs.inode_owner
    }

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

    const Repr: set<object> := {this} + fs.Repr

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
      forall ino: Ino | ino_ok(ino) ::
        && fs.inodes[ino].sz as nat == metadata[ino]
        && metadata[ino] <= Inode.MAX_SZ
    }

    static predicate inode_pos_match(ino: Ino, blks: seq<Blkno>, to_blkno: imap<Pos, Blkno>)
      requires ino_ok(ino)
      requires |blks| == 15
      requires pos_dom(to_blkno)
    {
      forall k: nat | k < 15 ::
        var bn := blks[k];
        && blkno_ok(bn)
        && to_blkno[Pos(ino, Idx.from_inode(k))] == bn
        // && (bn != 0 ==> blkno_pos(bn) == Some(MkPos(ino, Idx.from_inode(k))))
    }

    predicate {:opaque} ValidInodes()
      reads Repr
      requires ValidBasics()
    {
      forall ino:Ino | ino_ok(ino) ::
        inode_pos_match(ino, fs.inodes[ino].blks, to_blkno)
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

    predicate ValidIno(ino: Ino, i: Inode.Inode)
      reads this.Repr
    {
      && Valid()
      && fs.is_cur_inode(ino, i)
    }

    predicate ValidQ()
      reads Repr
    {
      && Valid()
      && fs.quiescent()
    }

    constructor Init(d: Disk)
      ensures Valid()
      ensures fs.quiescent()
      ensures data == imap pos: Pos | pos.idx.data? :: block0
      ensures metadata == map ino: Ino | ino_ok(ino) :: 0 as nat
    {
      this.fs := new Filesys.Init(d);
      this.to_blkno := imap pos: Pos {:trigger} :: 0 as Blkno;
      this.data := imap pos: Pos | pos.idx.data? :: block0;
      this.metadata := map ino: Ino | ino_ok(ino) :: 0 as nat;
      new;
      IndBlocks.to_blknos_zero();
      reveal ValidPos();
      reveal ValidInodes();
      reveal ValidIndirect();
      reveal ValidMetadata();
      reveal ValidData();
    }

    // private read
    method read_(txn: Txn, pos: Pos, i: Inode.Inode) returns (b: Bytes)
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
        var bn := i.blks[idx.k];
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

    twostate lemma {:timeLimitMultiplier 2} ValidInodes_change_one(pos: Pos, i': Inode.Inode, bn:Blkno)
      requires old(ValidBasics()) && ValidBasics()
      requires pos.ilevel == 0
      requires to_blkno == old(to_blkno[pos:=bn])
      requires fs.inodes == old(fs.inodes[pos.ino:=i'])
      requires fs.inode_owner == old(fs.inode_owner)
      requires blkno_ok(bn)
      requires i' == old(var i := fs.inodes[pos.ino]; i.(blks:=i.blks[pos.idx.k := bn]))
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
      && fs.inode_owner == old(fs.inode_owner)
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
    method {:timeLimitMultiplier 2} allocateRootMetadata(txn: Txn, pos: Pos, i: Inode.Inode)
      returns (ok: bool, i': Inode.Inode, bn: Blkno)
      modifies Repr
      requires has_jrnl(txn)
      requires ValidIno(pos.ino, i) ensures ValidIno(pos.ino, i')
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
        i' := i;
        Valid_unchanged();
        return;
      }

      i' := i.(blks := i.blks[idx.k := bn]);
      fs.writeInode(pos.ino, i');

      to_blkno := to_blkno[pos:=bn];
      var zeroblk := NewBytes(4096);
      fs.writeDataBlock(txn, bn, zeroblk);

      assert ValidPos() by {
        ValidPos_alloc_one(bn, pos);
      }
      assert ValidInodes() by {
        ValidInodes_change_one(pos, i', bn);
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
    method resolveMetadata(txn: Txn, pos: Pos, i: Inode.Inode) returns (ok: bool, i': Inode.Inode, bn: Blkno)
      decreases pos.ilevel
      modifies Repr
      requires has_jrnl(txn)
      requires ValidIno(pos.ino, i) ensures ValidIno(pos.ino, i')
      ensures ok ==> bn != 0 && bn == to_blkno[pos]
      ensures state_unchanged()
    {
      reveal ValidInodes();
      i' := i;
      var idx := pos.idx;
      if pos.ilevel == 0 {
        assert idx.off == IndOff.direct;
        bn := i.blks[idx.k];
        if bn != 0 {
          // we haven't actually written anything, just resolved existing metadata
          ok := true;
          return;
        }
        assert bn == 0;
        // need to allocate a top-level indirect block
        ok, i', bn := allocateRootMetadata(txn, pos, i');
        return;
      }
      // recurse
      var parent: Pos := pos.parent();
      var child: IndOff := pos.child();
      var ibn;
      ok, i', ibn := this.resolveMetadata(txn, parent, i');
      if !ok { return; }
      // now we have somewhere to store the reference to this block, but might
      // need to allocate into the parent
      var pblock := fs.getDataBlock(txn, ibn);
      bn := IndBlocks.decode_one(pblock, child.j);
      assert bn == to_blkno[pos] by {
        reveal ValidIndirect();
      }
      assert ValidIno(pos.ino, i');
      assert state_unchanged();
      if bn != 0 {
        return;
      }

      ok, bn := allocateIndirectMetadata(txn, pos, ibn, pblock);
      assert ValidIno(pos.ino, i');
      if !ok {
        return;
      }
    }

    // public
    //
    // data version of more general read_ spec
    method read(txn: Txn, pos: Pos, i: Inode.Inode) returns (b: Bytes)
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
    lemma inode_metadata(ino: Ino, i: Inode.Inode)
      requires ValidIno(ino, i)
      ensures i.sz as nat == metadata[ino]
    {
      reveal ValidMetadata();
    }

    lemma metadata_bound(ino: Ino)
      requires Valid()
      requires ino_ok(ino)
      ensures metadata[ino] <= Inode.MAX_SZ
    {
      reveal ValidMetadata();
    }

    method {:timeLimitMultiplier 2} write(txn: Txn, pos: Pos, i: Inode.Inode, blk: Bytes)
      returns (ok: bool, i':Inode.Inode)
      modifies Repr
      requires has_jrnl(txn)
      requires ValidIno(pos.ino, i)
      requires pos.data?
      requires is_block(blk.data)
      ensures ValidIno(pos.ino, i')
      ensures ok ==> data == old(data[pos := blk.data])
      ensures !ok ==> data == old(data)
      ensures metadata == old(metadata)
      ensures fs.inode_owner == old(fs.inode_owner)
    {
      i' := i;
      var idx := pos.idx;
      var bn;
      ok, i', bn := this.resolveMetadata(txn, pos, i');
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

    // public
    method startInode(txn: Txn, ino: Ino)
      returns (i: Inode.Inode)
      modifies fs
      requires ino_ok(ino)
      requires has_jrnl(txn)
      requires ValidQ()
      ensures ValidIno(ino, i)
      ensures fs.cur_inode == Some((ino, i))
      ensures state_unchanged()
    {
      i := fs.getInode(txn, ino);
      fs.startInode(ino, i);
      Valid_unchanged();
    }

    // public
    method writeInodeSz(ghost ino: Ino, i: Inode.Inode, sz': uint64)
      returns (i': Inode.Inode)
      modifies Repr
      requires ValidIno(ino, i)
      requires sz' <= Inode.MAX_SZ_u64
      ensures ValidIno(ino, i')
      ensures data == old(data)
      ensures metadata == old(metadata[ino := sz' as nat])
      ensures fs.inode_owner == old(fs.inode_owner)
    {
      reveal fsValid();
      i' := i.(sz := sz');
      fs.writeInode(ino, i');
      metadata := metadata[ino := sz' as nat];
      assert ValidBasics();
      assert ValidMetadata() by { reveal ValidMetadata(); }
      assert ValidInodes() by { reveal ValidInodes(); }
      assert ValidPos() by { reveal ValidPos(); }
      assert ValidIndirect() by { reveal ValidIndirect(); }
      assert ValidData() by { reveal ValidData(); }
    }

    // public
    method finishInode(txn: Txn, ino: Ino, i: Inode.Inode)
      modifies Repr
      requires ValidIno(ino, i)
      requires has_jrnl(txn)
      ensures ValidQ()
      ensures state_unchanged()
    {
      fs.finishInode(txn, ino, i);
      Valid_unchanged();
    }

    // public
    ghost method finishInodeReadonly(ino: Ino, i: Inode.Inode)
      modifies fs
      requires ValidIno(ino, i)
      requires fs.cur_inode == Some((ino, i))
      ensures ValidQ()
      ensures state_unchanged()
    {
      fs.finishInodeReadonly(ino, i);
      Valid_unchanged();
    }

    method allocInode(txn: Txn, ghost state: InodeAllocState) returns (ok: bool, ino: Ino)
      modifies fs.Repr
      requires Valid() ensures Valid()
      requires has_jrnl(txn)
      ensures data == old(data)
      ensures metadata == old(metadata)
      ensures fs.cur_inode == old(fs.cur_inode)
      ensures ok ==> ino_ok(ino)
      ensures ok ==> inode_owner() == old(inode_owner()[ino:=Some(state)])
      ensures ok ==> old(inode_owner()[ino].None?)
      ensures !ok ==> inode_owner() == old(inode_owner())
    {
      ok, ino := fs.allocateInode(txn, state);
      Valid_unchanged();
    }

  }

}
