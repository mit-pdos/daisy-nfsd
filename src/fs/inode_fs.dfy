include "../util/std.dfy"
include "../util/marshal.i.dfy"
include "../jrnl/jrnl.s.dfy"
include "super.dfy"
include "inode/mem_inode.dfy"

module InodeFs {
  import Arith
  import opened Std
  import C = Collections

  import Inode
  import opened MemInodes
  import Round
  import opened Machine
  import opened ByteSlice
  import opened JrnlTypes
  import opened JrnlSpec
  import opened Kinds
  import opened FsKinds
  import opened Marshal

  function zero_lookup(m: map<Blkno, Block>, bn: Blkno): Block
    requires blkno_dom(m)
    requires blkno_ok(bn)
  {
    if bn == 0
      then block0
      else m[bn]
  }

  predicate blkno_dom<T>(m: map<Blkno, T>)
  {
    forall bn: Blkno :: blkno_ok(bn) <==> bn in m
  }

  predicate ino_dom<T>(m: map<Ino, T>)
  {
    forall ino: Ino :: ino in m
  }

  class InodeFilesys<AllocState(!new)>
  {

    // inodes, block_used, and data_block are basically just the data in the
    // journal (except block_used additionally has inode owners)

    // encoded inodes on disk
    ghost var inodes: map<Ino, Inode.Inode>;
    ghost var cur_inode: Option<(Ino, Inode.Inode)>;
    // allocator state + some stuff
    ghost var block_used: map<Blkno, Option<AllocState>>;
    // on-disk value for all the data blocks
    ghost var data_block: map<Blkno, Block>;

    const jrnl: Jrnl;
    const balloc: Allocator;
    const ballocActualMax: uint64;

    static predicate Valid_basics(jrnl: Jrnl)
      reads jrnl
    {
      && jrnl.Valid()
      && jrnl.kinds == fs_kinds
    }

    predicate Valid_domains()
      reads this
    {
      && blkno_dom(block_used)
      && blkno_dom(data_block)
      && ino_dom(inodes)
    }

    predicate {:opaque} Valid_jrnl_super_block(actual_blocks: uint64)
      reads jrnl
      requires Valid_basics(jrnl)
    {
      super_block_inbounds(jrnl);
      jrnl.data[SuperBlkAddr] == ObjData(SuperBlock(super, actual_blocks).enc())
    }

    predicate {:opaque} Valid_jrnl_to_block_used(block_used: map<Blkno, Option<AllocState>>)
      reads jrnl
      requires blkno_dom(block_used)
      requires Valid_basics(jrnl)
    {
      blkno_bit_inbounds(jrnl);
      && (forall bn | blkno_ok(bn) ::
        && jrnl.data[DataBitAddr(bn)] == ObjBit(block_used[bn].Some?))
    }

    predicate {:opaque} Valid_jrnl_to_data_block(data_block: map<Blkno, Block>)
      reads jrnl
      requires blkno_dom(data_block)
      requires Valid_basics(jrnl)
    {
      && (forall bn | blkno_ok(bn) && bn != 0 ::
        datablk_inbounds(jrnl, bn);
        && jrnl.data[DataBlk(bn)] == ObjData(data_block[bn]))
    }

    predicate {:opaque} Valid_jrnl_to_data_block_except(data_block: map<Blkno, Block>, bn0: Blkno)
      reads jrnl
      requires blkno_dom(data_block)
      requires Valid_basics(jrnl)
    {
      && (forall bn | blkno_ok(bn) && bn != 0 && bn != bn0 ::
        datablk_inbounds(jrnl, bn);
        && jrnl.data[DataBlk(bn)] == ObjData(data_block[bn]))
    }

    predicate {:opaque} Valid_jrnl_to_inodes(inodes: map<Ino, Inode.Inode>)
      reads this, jrnl
      requires ino_dom(inodes)
      requires Valid_basics(jrnl)
    {
      forall ino: Ino ::
        inode_inbounds(jrnl, ino);
        if on_inode(ino)
          then jrnl.data[InodeAddr(ino)] == ObjData(Inode.enc(cur_inode.x.1))
          else jrnl.data[InodeAddr(ino)] == ObjData(Inode.enc(inodes[ino]))
    }

    predicate quiescent()
      reads this
    {
      cur_inode == None
    }

    predicate on_inode(ino: Ino)
      reads this
    {
      && cur_inode.Some?
      && cur_inode.x.0 == ino
    }

    static const ballocMax: uint64 := super.data_bitmaps as uint64 * (4096*8) - 8

    predicate Valid_balloc()
      reads this
    {
      && this.balloc.max == ballocActualMax <= ballocMax
      && this.balloc.Valid()
    }

    ghost const Repr: set<object> := {this, jrnl}

    predicate Valid()
      reads Repr
    {
      && Valid_basics(jrnl)
      && Valid_domains()
      && Valid_jrnl_super_block(ballocActualMax)
      && Valid_jrnl_to_block_used(block_used)
      && Valid_jrnl_to_data_block(data_block)
      && Valid_jrnl_to_inodes(inodes)
      && Valid_balloc()
    }

    predicate ValidExcept(bn: Blkno)
      reads Repr
    {
      && Valid_basics(jrnl)
      && Valid_domains()
      && Valid_jrnl_super_block(ballocActualMax)
      && Valid_jrnl_to_block_used(block_used)
      && Valid_jrnl_to_data_block_except(data_block, bn)
      && Valid_jrnl_to_inodes(inodes)
      && Valid_balloc()
      && blkno_ok(bn)
    }

    predicate ValidQ()
      reads Repr
    {
      && Valid()
      && quiescent()
    }

    constructor Init(d: Disk)
      ensures ValidQ()
      ensures fresh(Repr)
      ensures block_used == map bn: Blkno | blkno_ok(bn) :: None
      ensures cur_inode == None
      ensures inodes == map ino: Ino {:trigger} :: Inode.zero
      ensures data_block == map bn: Blkno | blkno_ok(bn) :: block0
    {
      var jrnl := NewJrnl(d, fs_kinds);
      this.jrnl := jrnl;
      var num_blks := DiskSize(d);
      var actual_max := ballocMax;
      if super_data_start+8 < num_blks <= actual_max {
        actual_max := Round.roundup64(num_blks - super_data_start - 8, 8);
        assert super_data_start + actual_max < num_blks;
      }
      var sb := SuperBlock(super, actual_max);
      var sb_bs := sb.encode();
      var txn := jrnl.Begin();
      super_block_inbounds(jrnl);
      txn.Write(SuperBlkAddr, sb_bs);
      var _ := txn.Commit(true);
      var balloc := NewAllocator(actual_max);
      this.balloc := balloc;
      this.ballocActualMax := actual_max;

      this.inodes := map ino: Ino {:trigger} :: Inode.zero;
      this.cur_inode := None;
      Inode.zero_encoding();
      this.block_used := map bn: uint64 | blkno_ok(bn) :: None;
      this.data_block := map bn: uint64 | blkno_ok(bn) :: block0;
      new;
      reveal jrnl.Valid();
      reveal addrsForKinds();

      reveal Valid_jrnl_super_block();
      reveal Valid_jrnl_to_block_used();
      reveal Valid_jrnl_to_data_block();
      reveal Valid_jrnl_to_inodes();
      reveal DataBlk();
      reveal InodeAddr();
    }

    // Recovery is needed for the file-system to recover its in-memory allocator
    // state. Due to the use of translation validation we don't have to prove
    // anything about how the used bits are recovered, but in practice they need
    // to be correct for the system to allocate any new blocks.
    constructor Recover(jrnl_: Jrnl, ghost fs: InodeFilesys<AllocState>)
      // not allowed to modify jrnl so can't break any invariants
      modifies {}
      requires fs.ValidQ()
      requires same_jrnl(jrnl_, fs.jrnl)
      ensures this.inodes == fs.inodes
      ensures this.cur_inode == fs.cur_inode
      ensures this.block_used == fs.block_used
      ensures this.data_block == fs.data_block;
      ensures this.ballocActualMax == fs.ballocActualMax
      ensures ValidQ()
      ensures fresh(Repr - {jrnl_})
      ensures this.jrnl == jrnl_
    {
      same_jrnl_valid();
      var txn := jrnl_.Begin();
      super_block_inbounds(jrnl_);
      var sb_bs := txn.Read(SuperBlkAddr, 4096*8);
      reveal fs.Valid_jrnl_super_block();
      var sb := SuperBlock.decode(sb_bs, SuperBlock(super, fs.ballocActualMax));
      var balloc := NewAllocator(sb.actual_blocks);

      blkno_bit_inbounds(jrnl_);
      var bn: Blkno := 1;
      while bn < sb.actual_blocks
        invariant txn.jrnl == jrnl_
        invariant Valid_basics(jrnl_)
        invariant balloc.Valid()
        invariant 1 <= bn as nat <= sb.actual_blocks as nat
      {
        var used := txn.ReadBit(DataBitAddr(bn));
        if used {
          balloc.MarkUsed(bn);
        }
        bn := bn + 1;
      }
      var ok := txn.Commit(true);
      expect ok, "recovery transaction failed";

      this.jrnl := jrnl_;
      this.balloc := balloc;
      this.ballocActualMax := sb.actual_blocks;

      // copy all ghost state
      inodes := fs.inodes;
      cur_inode := fs.cur_inode;
      block_used := fs.block_used;
      data_block := fs.data_block;

      new;
      reveal jrnl.Valid();
      reveal addrsForKinds();

      reveal Valid_jrnl_super_block();
      reveal Valid_jrnl_to_block_used();
      reveal Valid_jrnl_to_data_block();
      reveal Valid_jrnl_to_inodes();
      reveal DataBlk();
      reveal InodeAddr();
    }

    static predicate is_alloc_bn(bn: Blkno)
    {
      && 0 < bn < ballocMax
      && blkno_ok(bn)
    }

    // private
    method allocBlkno(txn: Txn) returns (ok:bool, bn:Blkno)
      requires txn.jrnl == this.jrnl
      requires Valid() ensures Valid()
      ensures ok ==>
        (&& is_alloc_bn(bn)
         && block_used[bn].None?
        )
    {
      bn := balloc.Alloc();
      if bn == 0 {
        return false, 0;
      }
      blkno_bit_inbounds(jrnl);
      var used := txn.ReadBit(DataBitAddr(bn));
      if used {
        print "block allocator returned used block ", bn, "\n";
        ok := false;
        balloc.Free(bn);
        return;
      }
      ok := true;
      reveal Valid_jrnl_to_block_used();
    }

    // public
    method getDataBlock(txn: Txn, bn: Blkno) returns (bs: Bytes)
      modifies {}
      requires Valid() ensures Valid()
      requires this.jrnl == txn.jrnl
      requires blkno_ok(bn)
      ensures fresh(bs)
      ensures is_block(bs.data)
      ensures bs.data == zero_lookup(data_block, bn)
    {
      if bn == 0 {
        bs := NewBytes(4096);
        return;
      }
      datablk_inbounds(jrnl, bn);
      bs := txn.Read(DataBlk(bn), 4096*8);
      reveal Valid_jrnl_to_data_block();
    }

    // public
    method writeDataBlock(txn: Txn, bn: Blkno, blk: Bytes)
      modifies this, jrnl, blk
      requires Valid() ensures Valid()
      requires txn.jrnl == jrnl
      requires is_block(blk.data)
      requires bn != 0 && blkno_ok(bn)
      ensures
      && inodes == old(inodes)
      && cur_inode == old(cur_inode)
      && block_used == old(block_used)
      && data_block == old(data_block[bn := blk.data])
    {
      addException(bn);
      fakeWriteDataBlock(bn, blk.data);
      finishWriteDataBlock(txn, bn, blk);
    }

    // public
    ghost method fakeWriteDataBlock(bn: Blkno, blk: Block)
      modifies this
      requires ValidExcept(bn) ensures ValidExcept(bn)
      requires bn != 0 && blkno_ok(bn)
      ensures
      && inodes == old(inodes)
      && cur_inode == old(cur_inode)
      && block_used == old(block_used)
      && data_block == old(data_block)[bn := blk]
    {
      data_block := data_block[bn := blk];
      assert ValidExcept(bn) by {
        reveal Valid_jrnl_super_block();
        reveal Valid_jrnl_to_block_used();
        reveal Valid_jrnl_to_data_block();
        reveal Valid_jrnl_to_data_block_except();
        reveal Valid_jrnl_to_inodes();
      }
    }

    ghost method addException(bn: Blkno)
      requires blkno_ok(bn)
      requires Valid() ensures ValidExcept(bn)
    {
        reveal Valid_jrnl_super_block();
        reveal Valid_jrnl_to_block_used();
        reveal Valid_jrnl_to_data_block();
        reveal Valid_jrnl_to_data_block_except();
        reveal Valid_jrnl_to_inodes();
    }

    method finishWriteDataBlock(txn: Txn, bn: Blkno, blk: Bytes)
      modifies jrnl, blk
      requires txn.jrnl == jrnl
      requires ValidExcept(bn) ensures Valid()
      requires blk.data == data_block[bn]
      ensures blk.data == []
      ensures
      && inodes == old(inodes)
      && cur_inode == old(cur_inode)
      && block_used == old(block_used)
      && data_block == old(data_block)
    {
      datablk_inbounds(jrnl, bn);
      txn.Write(DataBlk(bn), blk);
      assert Valid() by {
        reveal Valid_jrnl_super_block();
        reveal Valid_jrnl_to_block_used();
        reveal Valid_jrnl_to_data_block();
        reveal Valid_jrnl_to_data_block_except();
        reveal Valid_jrnl_to_inodes();
        FsKinds.DataBlk_disjoint(bn);
        reveal_DataBlk();
      }
    }

    predicate is_inode(ino: Ino, i: Inode.Inode)
      reads this, jrnl
      requires Valid_basics(jrnl)
      requires Valid_domains()
    {
      && inodes[ino] == i
    }

    predicate is_cur_inode(ino: Ino, i: Inode.Inode)
      reads this, jrnl
      requires Valid_basics(jrnl)
      requires Valid_domains()
    {
      && is_inode(ino, i)
      && on_inode(ino)
    }

    // public
    ghost method startInode(ino: Ino, i: Inode.Inode)
      modifies this
      requires ValidQ()
      requires is_inode(ino, i)
      ensures Valid()
      ensures is_cur_inode(ino, i)
      ensures cur_inode == Some((ino, i))
      ensures inodes == old(inodes)
      ensures block_used == old(block_used)
      ensures data_block == old(data_block)
    {
      cur_inode := Some( (ino, i) );
      reveal_Valid_jrnl_to_inodes();
    }

    // public
    method finishInode(txn: Txn, ino: Ino, i: MemInode)
      modifies this, jrnl, i.bs
      requires Valid()
      requires on_inode(ino)
      requires txn.jrnl == this.jrnl
      requires i.Valid()
      requires is_inode(ino, i.val())
      ensures ValidQ()
      ensures inodes == old(inodes)
      ensures data_block == old(data_block)
      ensures block_used == old(block_used)
    {
      cur_inode := None;
      inode_inbounds(jrnl, ino);
      var buf' := i.encode();
      txn.Write(InodeAddr(ino), buf');
      assert jrnl.data[InodeAddr(ino)] == ObjData(Inode.enc(inodes[ino]));
      assert Valid_jrnl_to_inodes(inodes) by {
        reveal_Valid_jrnl_to_inodes();
        InodeAddr_inj();
        // NOTE: good example of debugging
        // forall ino':Ino
        //   ensures jrnl.data[InodeAddr(ino')] == ObjData(Inode.enc(inodes[ino']))
        // {
        //   if ino' == ino {} else {
        //     assert InodeAddr(ino) != InodeAddr(ino') by {
        //       reveal_InodeAddr();
        //     }
        //   }
        // }
      }
      assert Valid() by {
        reveal Valid_jrnl_super_block();
        reveal Valid_jrnl_to_data_block();
        reveal Valid_jrnl_to_block_used();
      }
    }

    // For read-only calls, we can still use the on_inode machinery to "focus"
    // on an inode but also keep track of the fact that the inode doesn't need
    // to be written back out. Then finishInodeReadonly allows to restore the
    // quiescent state without involving the transaction.
    ghost method finishInodeReadonly(ino: Ino, i: Inode.Inode)
      modifies this
      requires Valid()
      requires is_inode(ino, i)
      requires cur_inode == Some((ino, i))
      ensures ValidQ()
      ensures inodes == old(inodes)
      ensures data_block == old(data_block)
      ensures block_used == old(block_used)
    {
      cur_inode := None;
      assert Valid_jrnl_to_inodes(inodes) by {
        reveal Valid_jrnl_to_inodes();
      }
      assert Valid() by {
        reveal Valid_jrnl_to_data_block();
        reveal Valid_jrnl_to_block_used();
      }
    }

    method lockInode(txn: Txn, ino: Ino)
      modifies {}
      requires Valid()
      requires txn.jrnl == jrnl
    {
      reveal_Valid_jrnl_to_inodes();
      inode_inbounds(jrnl, ino);
      var _ := txn.Read(InodeAddr(ino), 128*8);
    }

    method lockInodes(txn: Txn, inos: seq<uint64>)
      modifies {}
      requires Valid()
      requires txn.jrnl == jrnl
    {
      if |inos| == 0 {}
      else {
        var ino := inos[0];
        var ok := is_ino_ok(ino);
        if ok {
          lockInode(txn, ino);
        }
        lockInodes(txn, inos[1..]);
      }
    }

    // public
    method getInode(txn: Txn, ino: Ino) returns (i: MemInode)
      modifies {}
      requires ValidQ()
      requires txn.jrnl == jrnl
      ensures i.Valid()
      ensures is_inode(ino, i.val())
      ensures fresh(i.Repr)
    {
      reveal_Valid_jrnl_to_inodes();
      inode_inbounds(jrnl, ino);
      var buf := txn.Read(InodeAddr(ino), 128*8);
      i := new MemInode(buf, inodes[ino]);
    }

    // public
    ghost method writeInode(ino: Ino, i': MemInode)
      modifies this
      requires Valid() ensures Valid()
      requires on_inode(ino);
      requires i'.Valid()
      ensures is_cur_inode(ino, i'.val())
      ensures inodes == old(inodes)[ino:=i'.val()]
      ensures block_used == old(block_used)
      ensures data_block == old(data_block)
      ensures cur_inode == old(cur_inode)
    {
      inodes := inodes[ino:=i'.val()];

      assert Valid() by {
        reveal Valid_jrnl_super_block();
        reveal Valid_jrnl_to_block_used();
        reveal Valid_jrnl_to_data_block();
        reveal Valid_jrnl_to_inodes();
      }
    }

    // public
    method allocateTo(txn: Txn, ghost state: AllocState)
      returns (ok: bool, bn:Blkno)
      modifies Repr
      requires Valid() ensures Valid()
      requires txn.jrnl == jrnl
      ensures inodes == old(inodes)
      ensures cur_inode == old(cur_inode)
      ensures data_block == old(data_block)
      ensures !ok ==> block_used == old(block_used)
      ensures ok ==> block_used == old(block_used[bn:=Some(state)])
      ensures ok ==> is_alloc_bn(bn)
      ensures ok ==> old(block_used[bn].None?)
    {
      ok, bn := allocBlkno(txn);
      if !ok {
        return;
      }

      blkno_bit_inbounds(jrnl);
      block_used := block_used[bn:=Some(state)];
      txn.WriteBit(DataBitAddr(bn), true);

      assert Valid() by {
        reveal Valid_jrnl_super_block();
        reveal Valid_jrnl_to_block_used();
        reveal Valid_jrnl_to_data_block();
        reveal Valid_jrnl_to_inodes();
        DataBitAddr_disjoint(bn);
      }

      return;
    }

    method free(txn: Txn, bn: Blkno)
      modifies Repr
      requires Valid() ensures Valid()
      requires txn.jrnl == jrnl
      requires blkno_ok(bn)
      requires block_used[bn].Some?
      ensures inodes == old(inodes)
      ensures block_used == old(block_used[bn:=None])
      ensures cur_inode == old(cur_inode)
      ensures data_block == old(data_block)
    {
      blkno_bit_inbounds(jrnl);
      block_used := block_used[bn:=None];
      txn.WriteBit(DataBitAddr(bn), false);
      if 0 < bn < ballocActualMax {
        balloc.Free(bn);
      }

      assert Valid() by {
        reveal Valid_jrnl_super_block();
        reveal Valid_jrnl_to_block_used();
        reveal Valid_jrnl_to_data_block();
        reveal Valid_jrnl_to_inodes();
        DataBitAddr_disjoint(bn);
      }
    }

    method freeWithException(txn: Txn, bn: Blkno, ghost bn0: Blkno)
      modifies Repr
      requires ValidExcept(bn0) ensures ValidExcept(bn0)
      requires txn.jrnl == jrnl
      requires blkno_ok(bn)
      requires block_used[bn].Some?
      ensures inodes == old(inodes)
      ensures block_used == old(block_used[bn:=None])
      ensures cur_inode == old(cur_inode)
      ensures data_block == old(data_block)
    {
      blkno_bit_inbounds(jrnl);
      block_used := block_used[bn:=None];
      txn.WriteBit(DataBitAddr(bn), false);
      if 0 < bn < ballocActualMax {
        balloc.Free(bn);
      }

      assert ValidExcept(bn0) by {
        reveal Valid_jrnl_super_block();
        reveal Valid_jrnl_to_block_used();
        reveal Valid_jrnl_to_data_block();
        reveal Valid_jrnl_to_data_block_except();
        reveal Valid_jrnl_to_inodes();
        DataBitAddr_disjoint(bn);
      }
    }

    // public
    method Size(ino: Ino) returns (sz: uint64)
      modifies {}
      requires ValidQ()
      ensures sz as nat == inodes[ino].sz as nat
    {
      var txn := jrnl.Begin();
      var i := getInode(txn, ino);
      sz := i.sz;
      var _ := txn.Commit(true);
    }

    method TotalBytes() returns (sz: uint64)
      requires Valid()
    {
      return ballocActualMax*4096;
    }

    method FreeBytes() returns (sz: uint64)
      requires Valid()
    {
      var num_blocks := balloc.NumFree();
      return num_blocks * 4096;
    }
  }
}
