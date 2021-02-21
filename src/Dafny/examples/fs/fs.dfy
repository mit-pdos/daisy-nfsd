include "../../util/marshal.i.dfy"
include "../../jrnl/jrnl.s.dfy"
include "../../jrnl/alloc.i.dfy"
include "kinds.dfy"
include "inode.dfy"

module Fs {
  import Inode
  import C = Collections
  import Arith
  import Round
  import opened Machine
  import opened ByteSlice
  import opened JrnlTypes
  import opened JrnlSpec
  import opened Alloc
  import opened Kinds
  import opened FsKinds
  import opened Marshal

  datatype Option<T> = Some(x:T) | None

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
    forall ino: Ino :: ino_ok(ino) <==> ino in m
  }

  class Filesys<AllocState>
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
    const balloc: MaxAllocator;

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

    predicate {:opaque} Valid_jrnl_to_inodes(inodes: map<Ino, Inode.Inode>)
      reads this, jrnl
      requires ino_dom(inodes)
      requires Valid_basics(jrnl)
    {
      forall ino: Ino | ino_ok(ino) ::
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
      && ino_ok(ino)
      && cur_inode.Some?
      && cur_inode.x.0 == ino
    }

    static const ballocMax: uint64 := super.data_bitmaps as uint64 * 4096*8 - 8

    predicate Valid_balloc()
      reads this
    {
      && this.balloc.max == ballocMax
      && this.balloc.Valid()
    }

    predicate Valid_jrnl_to_all()
      reads this, jrnl
    {
      && Valid_basics(jrnl)
      && Valid_domains()
      && Valid_jrnl_to_block_used(block_used)
      && Valid_jrnl_to_data_block(data_block)
      && Valid_jrnl_to_inodes(inodes)
    }

    function Repr(): set<object>
    {
      {this, jrnl} + balloc.Repr()
    }

    static predicate Valid_data_block(data_block: map<Blkno, Block>)
    {
      forall bn | bn in data_block :: is_block(data_block[bn])
    }

    predicate Valid()
      reads Repr()
    {
      && Valid_data_block(data_block)
      && Valid_jrnl_to_all()

      && this.Valid_balloc()
    }

    predicate ValidQ()
      reads Repr()
    {
      && Valid()
      && quiescent()
    }

    constructor Init(d: Disk)
      ensures ValidQ()
      ensures block_used == map bn: Blkno | blkno_ok(bn) :: None
      ensures cur_inode == None
      ensures inodes == map ino: Ino | ino_ok(ino) :: Inode.zero
      ensures data_block == map bn: Blkno | blkno_ok(bn) :: block0
    {
      var jrnl := NewJrnl(d, fs_kinds);
      this.jrnl := jrnl;
      var balloc := new MaxAllocator(ballocMax);
      this.balloc := balloc;

      this.inodes := map ino: Ino | ino_ok(ino) :: Inode.zero;
      this.cur_inode := None;
      Inode.zero_encoding();
      this.block_used := map bn: uint64 | blkno_ok(bn) :: None;
      this.data_block := map bn: uint64 | blkno_ok(bn) :: block0;
      new;
      reveal jrnl.Valid();
      reveal addrsForKinds();

      reveal Valid_jrnl_to_block_used();
      reveal Valid_jrnl_to_data_block();
      reveal Valid_jrnl_to_inodes();
      reveal DataBlk();
      reveal InodeAddr();
    }

    // Recovery is needed for the file-system to recover its in-memory allocator
    // state. Due to the use of translation validation (that is, we don't prove
    // the allocator has the right free elements but check the on-disk value) we
    // don't have to re-establish any invariant here, but without this code on
    // recovery the allocator will give out used addresses and fail in practice.
    constructor Recover(jrnl_: Jrnl)
      // not allowed to modify jrnl so can't break any invariants
      modifies {}
      requires Valid_basics(jrnl_)
      ensures this.jrnl == jrnl_
    {
      var balloc := new MaxAllocator(ballocMax);

      var txn := jrnl_.Begin();
      blkno_bit_inbounds(jrnl_);
      var bn: Blkno := 1;
      while bn < ballocMax
        modifies balloc.Repr()
        invariant txn.jrnl == jrnl_
        invariant Valid_basics(jrnl_)
        invariant balloc.Valid()
        invariant 1 <= bn as nat <= ballocMax as nat
      {
        var used := txn.ReadBit(DataBitAddr(bn));
        if used {
          balloc.MarkUsed(bn);
        }
        bn := bn + 1;
      }

      this.jrnl := jrnl_;
      this.balloc := balloc;
    }

    static predicate is_alloc_bn(bn: Blkno)
    {
      && 0 < bn < ballocMax
      && blkno_ok(bn)
    }

    // private
    method allocBlkno(txn: Txn) returns (ok:bool, bn:Blkno)
      modifies balloc.Repr()
      requires txn.jrnl == this.jrnl
      requires Valid() ensures Valid()
      ensures ok ==>
        (&& is_alloc_bn(bn)
         && block_used[bn].None?
        )
    {
      bn := balloc.Alloc();
      blkno_bit_inbounds(jrnl);
      var used := txn.ReadBit(DataBitAddr(bn));
      if used {
        ok := false;
        balloc.Free(bn);
        return;
      }
      ok := true;
      reveal_Valid_jrnl_to_block_used();
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
      reveal_Valid_jrnl_to_data_block();
    }

    // public
    method writeDataBlock(txn: Txn, bn: Blkno, blk: Bytes)
      modifies this, jrnl
      requires Valid() ensures Valid()
      requires txn.jrnl == jrnl
      requires is_block(blk.data)
      requires bn != 0 && blkno_ok(bn)
      ensures
      && inodes == old(inodes)
      && cur_inode == old(cur_inode)
      && block_used == old(block_used)
      && data_block == old(data_block)[bn := blk.data]
    {
      datablk_inbounds(jrnl, bn);
      txn.Write(DataBlk(bn), blk);
      data_block := data_block[bn := blk.data];

      assert Valid_jrnl_to_all() by {
        reveal_Valid_jrnl_to_block_used();
        reveal_Valid_jrnl_to_data_block();
        reveal_Valid_jrnl_to_inodes();
        FsKinds.DataBlk_disjoint(bn);
        reveal_DataBlk();
      }
    }

    predicate is_inode(ino: Ino, i: Inode.Inode)
      reads this, jrnl
      requires Valid_basics(jrnl)
      requires Valid_domains()
    {
      && ino_ok(ino)
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
    method finishInode(txn: Txn, ino: Ino, i: Inode.Inode)
      modifies this, jrnl
      requires Valid()
      requires on_inode(ino)
      requires txn.jrnl == this.jrnl
      requires is_inode(ino, i)
      ensures ValidQ()
      ensures inodes == old(inodes)
      ensures data_block == old(data_block)
      ensures block_used == old(block_used)
    {
      cur_inode := None;
      inode_inbounds(jrnl, ino);
      var buf' := Inode.encode_ino(i);
      txn.Write(InodeAddr(ino), buf');
      assert jrnl.data[InodeAddr(ino)] == ObjData(Inode.enc(inodes[ino]));
      assert Valid_jrnl_to_inodes(inodes) by {
        reveal_Valid_jrnl_to_inodes();
        InodeAddr_inj();
        // NOTE: good example of debugging
        // forall ino' | ino_ok(ino')
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
        reveal_Valid_jrnl_to_data_block();
        reveal_Valid_jrnl_to_block_used();
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

    // public
    method getInode(txn: Txn, ino: Ino) returns (i:Inode.Inode)
      modifies {}
      requires ValidQ()
      requires ino_ok(ino)
      requires txn.jrnl == jrnl
      ensures is_inode(ino, i)
    {
      reveal_Valid_jrnl_to_inodes();
      inode_inbounds(jrnl, ino);
      var buf := txn.Read(InodeAddr(ino), 128*8);
      i := Inode.decode_ino(buf, inodes[ino]);
    }

    // public
    ghost method writeInode(ino: Ino, i': Inode.Inode)
      modifies this
      requires Valid() ensures Valid()
      requires on_inode(ino);
      requires i'.Valid()
      ensures is_cur_inode(ino, i')
      ensures inodes == old(inodes)[ino:=i']
      ensures block_used == old(block_used)
      ensures data_block == old(data_block)
      ensures cur_inode == old(cur_inode)
    {
      inodes := inodes[ino:=i'];

      assert Valid_jrnl_to_all() by {
        reveal_Valid_jrnl_to_block_used();
        reveal_Valid_jrnl_to_data_block();
        reveal_Valid_jrnl_to_inodes();
      }
    }

    // public
    method allocateTo(txn: Txn, ghost state: AllocState)
      returns (ok: bool, bn:Blkno)
      modifies Repr()
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

      assert Valid_jrnl_to_all() by {
        reveal_Valid_jrnl_to_block_used();
        reveal_Valid_jrnl_to_data_block();
        reveal_Valid_jrnl_to_inodes();
        DataBitAddr_disjoint(bn);
      }

      return;
    }

    method free(txn: Txn, bn: Blkno)
      modifies Repr()
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

      assert Valid_jrnl_to_all() by {
        reveal_Valid_jrnl_to_block_used();
        reveal_Valid_jrnl_to_data_block();
        reveal_Valid_jrnl_to_inodes();
        DataBitAddr_disjoint(bn);
      }
    }

    // public
    method Size(ino: Ino) returns (sz: uint64)
      modifies {}
      requires ValidQ()
      requires ino_ok(ino)
      ensures sz as nat == inodes[ino].sz as nat
    {
      var txn := jrnl.Begin();
      var i := getInode(txn, ino);
      sz := i.sz;
      var _ := txn.Commit();
    }
  }
}
