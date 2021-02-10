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
  import opened JrnlSpec
  import opened Alloc
  import opened Kinds
  import opened FsKinds
  import opened Marshal

  datatype Option<T> = Some(x:T) | None

  type Block = seq<byte>
  predicate is_block(b: Block) { |b| == 4096 }
  datatype InodeData = InodeData(sz: nat, blks: seq<Block>)
  {
    static const zero: InodeData := InodeData(0, C.repeat(block0, 15))

    const num_used: nat := Round.div_roundup_alt(sz, 4096)

    predicate Valid()
    {
      && |blks| == 15
      && sz <= Inode.MAX_SZ
      && (forall blk | blk in blks :: is_block(blk))
    }

    static lemma zero_valid()
      ensures zero.Valid()
    {}

    function used_blocks(): seq<Block>
      requires Valid()
    {
      blks[..num_used]
    }

    lemma used_blocks_valid()
      requires Valid()
      ensures |used_blocks()| == num_used
      ensures forall blk | blk in used_blocks() :: is_block(blk)
    {}
  }

  function zero_lookup(m: map<Blkno, Block>, bn: Blkno): Block
    requires blkno_dom(m)
    requires blkno_ok(bn)
  {
    if bn == 0
      then block0
      else m[bn]
  }

  const block0: Block := C.repeat(0 as byte, 4096)
  lemma block0_ok()
    ensures is_block(block0)
  {}

  predicate blkno_dom<T>(m: map<Blkno, T>)
  {
    forall bn: Blkno :: blkno_ok(bn) <==> bn in m
  }

  predicate ino_dom<T>(m: map<Ino, T>)
  {
    forall ino: Ino :: ino_ok(ino) <==> ino in m
  }

  predicate Valid_inode_blks(inode_blks: map<Ino, InodeData>)
    requires ino_dom(inode_blks)
  {
    forall ino | ino_ok(ino) :: inode_blks[ino].Valid()
  }

  class Filesys
  {

    // block-based inodes
    ghost var inode_blks: map<Ino, InodeData>;

    // inodes, block_used, and data_block are basically just the data in the
    // journal (except block_used additionally has inode owners)

    // encoded inodes on disk
    ghost var inodes: map<Ino, Inode.Inode>;
    ghost var cur_inode: Option<(Ino, Inode.Inode)>;
    // allocator state + the inode that owns the block
    ghost var block_used: map<Blkno, Option<Ino>>;
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
      && ino_dom(inode_blks)
    }

    predicate {:opaque} Valid_jrnl_to_block_used(block_used: map<Blkno, Option<Ino>>)
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

    static predicate Inodes_all_Valid(inodes: map<Ino, Inode.Inode>)
    {
      forall ino: Ino | ino in inodes :: inodes[ino].Valid()
    }

    static predicate {:opaque} Valid_inodes_to_block_used(inodes: map<Ino, Inode.Inode>, block_used: map<Blkno, Option<Ino>>)
      requires blkno_dom(block_used)
    {
      && (forall ino: Ino | ino in inodes ::
        && (forall bn | bn in inodes[ino].blks ::
          bn != 0 ==>
          && blkno_ok(bn)
          && block_used[bn] == Some(ino))
        )
    }

    predicate Valid_inodes()
      requires Valid_domains()
      reads this
    {
      && Inodes_all_Valid(inodes)
      && Valid_inodes_to_block_used(inodes, block_used)
    }

    static predicate {:opaque} blks_match?(blk_offs: seq<Blkno>, blks: seq<Block>, data_block: map<Blkno, Block>)
      requires |blk_offs| == |blks|
      requires blkno_dom(data_block)
    {
      forall k: nat | k < |blk_offs| ::
        && blkno_ok(blk_offs[k])
        && blks[k] == zero_lookup(data_block, blk_offs[k])
    }

    // inode i encodes blks, using data_block to lookup indirect references
    static predicate inode_blks_match(i: Inode.Inode, d: InodeData, data_block: map<Blkno, Block>)
    {
      && i.sz as nat == d.sz
      && |d.blks| == |i.blks|
      && d.Valid()
      && blkno_dom(data_block)
      && blks_match?(i.blks, d.blks, data_block)
    }

    static predicate Valid_inode_blks_match(
      inodes: map<Ino, Inode.Inode>,
      inode_blks: map<Ino, InodeData>,
      data_block: map<Blkno, Block>)
      requires ino_dom(inodes)
      requires ino_dom(inode_blks)
      requires blkno_dom(data_block)
    {
      && (forall ino: Ino | ino_ok(ino) ::
         && inode_blks_match(inodes[ino], inode_blks[ino], data_block))
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

    predicate Valid_data()
      reads this
      requires Valid_domains()
    {
      && Valid_inode_blks_match(inodes, inode_blks, data_block)
    }

    lemma inode_blks_sz(ino: Ino)
      requires Valid_domains()
      requires Valid_data()
      requires ino_ok(ino)
      ensures inodes[ino].sz as nat == inode_blks[ino].sz
    {
      assert inode_blks_match(inodes[ino], inode_blks[ino], data_block);
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
      && this.Valid_inodes()
      && this.Valid_data()

      && this.Valid_balloc()
    }

    predicate ValidQ()
      reads Repr()
    {
      && Valid()
      && quiescent()
    }

    lemma Valid_inode_data()
      requires Valid_domains()
      requires Valid_data()
      ensures Valid_inode_blks(inode_blks)
    {}

    constructor Init(d: Disk)
      ensures ValidQ()
      ensures inode_blks == map ino | ino_ok(ino) :: InodeData.zero
    {
      var jrnl := NewJrnl(d, fs_kinds);
      this.jrnl := jrnl;
      var balloc := new MaxAllocator(ballocMax);
      this.balloc := balloc;

      this.inodes := map ino: Ino | ino_ok(ino) :: Inode.zero;
      this.cur_inode := None;
      this.inode_blks := map ino: Ino | ino_ok(ino) :: InodeData.zero;
      Inode.zero_encoding();
      this.block_used := map bn: uint64 | blkno_ok(bn) :: None;
      this.data_block := map bn: uint64 | blkno_ok(bn) :: zeroObject(KindBlock).bs;
      new;
      InodeData.zero_valid();
      jrnl.reveal_Valid();
      reveal_Valid_inodes_to_block_used();
      reveal_addrsForKinds();

      reveal_Valid_jrnl_to_block_used();
      reveal_Valid_jrnl_to_data_block();
      reveal_Valid_jrnl_to_inodes();
      reveal_blks_match?();
      reveal_DataBlk();
      reveal_InodeAddr();
      assert Valid_inodes();
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

    // full block append
    static function method inode_append(i: Inode.Inode, bn: Blkno): (i':Inode.Inode)
    requires i.Valid()
    {

      Inode.Mk(i.sz + 4096, i.blks + [bn])
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

    lemma free_block_unused(bn: Blkno)
      requires Valid()
      requires bn != 0
      requires blkno_ok(bn) && block_used[bn].None?
      ensures forall ino | ino_ok(ino) :: bn !in inodes[ino].blks
    {
      reveal_Valid_inodes_to_block_used();
    }

    // public
    method writeDataBlock(txn: Txn, bn: Blkno, blk: Bytes,
      ghost ino: Ino, ghost blkoff: nat)
      modifies this, jrnl
      requires Valid() ensures Valid()
      requires txn.jrnl == jrnl
      requires is_block(blk.data)
      requires ino_ok(ino)
      requires blkoff < |inode_blks[ino].blks|
      requires inodes[ino].blks[blkoff] == bn
      requires bn != 0
      ensures
      && inodes == old(inodes)
      && cur_inode == old(cur_inode)
      && block_used == old(block_used)
      && data_block == old(data_block)[bn := blk.data]
      && inode_blks ==
        old(var d0 := inode_blks[ino];
            var d' := d0.(blks := d0.blks[blkoff:=blk.data]);
            inode_blks[ino:=d'])
    {
      assert inode_blks_match(inodes[ino], inode_blks[ino], data_block);
      reveal_blks_match?();
      datablk_inbounds(jrnl, bn);
      txn.Write(DataBlk(bn), blk);
      data_block := data_block[bn := blk.data];
      ghost var d0 := inode_blks[ino];
      ghost var d' := d0.(blks := d0.blks[blkoff:=blk.data]);
      inode_blks := inode_blks[ino:=d'];

      ghost var i := inodes[ino];
      inode_blks_match_change_1(i, d0, old(data_block), i, bn, blkoff, blk.data);

      Filesys.reveal_Valid_inodes_to_block_used();
      assert Inodes_all_Valid(inodes);
      ghost var this_ino := ino;
      forall ino | ino_ok(ino)
        ensures inode_blks_match(inodes[ino], inode_blks[ino], data_block)
      {
        inode_blks_match_change_other(ino, old(inode_blks[ino]),
          old(inodes), old(data_block), old(block_used),
          this_ino, bn, blk.data);
      }

      assert Valid_jrnl_to_all() by {
        reveal_Valid_jrnl_to_block_used();
        reveal_Valid_jrnl_to_data_block();
        reveal_Valid_jrnl_to_inodes();
        FsKinds.DataBlk_disjoint(bn);
        reveal_DataBlk();
      }
    }

    // public
    ghost method startInode(ino: Ino, i: Inode.Inode)
      modifies this
      requires ValidQ()
      requires is_inode(ino, i)
      ensures Valid()
      ensures is_cur_inode(ino, i)
      ensures inode_blks == old(inode_blks)
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
      ensures inode_blks == old(inode_blks)
      ensures inodes == old(inodes)
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

    // private
    ghost method writeInode(ino: Ino, i': Inode.Inode)
      modifies this, jrnl
      requires Valid_jrnl_to_all() ensures Valid_jrnl_to_all()
      requires Inodes_all_Valid(inodes) ensures Inodes_all_Valid(inodes)
      requires on_inode(ino);
      requires i'.Valid()
      ensures is_cur_inode(ino, i')
      ensures inodes == old(inodes)[ino:=i']
      ensures block_used == old(block_used)
      ensures data_block == old(data_block)
      ensures inode_blks == old(inode_blks)
    {
      inodes := inodes[ino:=i'];

      assert Valid_jrnl_to_all() by {
        reveal_Valid_jrnl_to_block_used();
        reveal_Valid_jrnl_to_data_block();
        reveal_Valid_jrnl_to_inodes();
      }
    }

    // public
    ghost method writeInodeSz(ino: Ino, i: Inode.Inode, i': Inode.Inode)
      modifies this, jrnl
      requires Valid() ensures Valid()
      requires is_cur_inode(ino, i)
      requires i'.blks == i.blks
      requires i'.Valid()
      ensures is_cur_inode(ino, i')
      ensures
      && inodes == old(inodes)[ino:=i']
      && block_used == old(block_used)
      && data_block == old(data_block)
      && inode_blks == old(inode_blks[ino:=inode_blks[ino].(sz := i'.sz as nat)])
    {
      writeInode(ino, i');
      inode_blks := inode_blks[ino:=inode_blks[ino].(sz := i'.sz as nat)];
      assert Valid() by {
        reveal_Valid_inodes_to_block_used();
        reveal_Valid_jrnl_to_inodes();
      }
    }

    static lemma inode_blks_match_change_1(
      i: Inode.Inode, d: InodeData, data_block: map<Blkno, seq<byte>>,
      i': Inode.Inode, bn: Blkno, blkoff: nat, bs: seq<byte>)
      requires inode_blks_match(i, d, data_block)
      requires blkoff < |i.blks|
      requires |bs| == 4096
      requires i.Valid()
      requires i'.Valid()
      requires i'.blks == i.blks
      requires bn in data_block
      requires bn != 0
      requires i.blks[blkoff] == bn
      ensures inode_blks_match(i', InodeData(i'.sz as nat, d.blks[blkoff:=bs]), data_block[bn := bs])
    {
      Inode.reveal_blks_unique();
      reveal_blks_match?();
    }

    // inode_blks_match is insensitive to changes in blocks owned by other inodes
    static lemma inode_blks_match_change_other(
      ino: Ino, d: InodeData,
      inodes: map<Ino, Inode.Inode>,
      data_block: map<Blkno, seq<byte>>,
      block_used: map<Blkno, Option<Ino>>,
      // stuff that changed in an unrelated inode ino':
      ino': Ino, bn: Blkno, bs: seq<byte>)
      requires && blkno_dom(data_block) && blkno_dom(block_used) && blkno_ok(bn)
      requires && ino_dom(inodes) && ino_ok(ino) && ino_ok(ino')
      requires inode_blks_match(inodes[ino], d, data_block)
      requires Valid_inodes_to_block_used(inodes, block_used)
      requires block_used[bn] == Some(ino')
      ensures ino != ino' ==> inode_blks_match(inodes[ino], d, data_block[bn:=bs])
    {
      reveal_Valid_inodes_to_block_used();
      reveal_blks_match?();
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

    // private
    method allocateTo(txn: Txn, ghost ino: Ino, ghost i: Inode.Inode) returns (ok: bool, bn:Blkno)
      modifies Repr()
      requires Valid() ensures Valid()
      requires txn.jrnl == jrnl
      requires is_inode(ino, i)
      ensures inode_blks == old(inode_blks)
      ensures inodes == old(inodes)
      ensures cur_inode == old(cur_inode)
      ensures !ok ==> block_used == old(block_used)
      ensures data_block == old(data_block)
      ensures ok ==> forall ino | ino_ok(ino) :: bn !in inodes[ino].blks
      ensures ok ==> block_used == old(block_used[bn:=Some(ino)])
      ensures ok ==> is_alloc_bn(bn)
      ensures ok ==> old(block_used[bn].None?)
    {
      ok, bn := allocBlkno(txn);
      if !ok {
        return;
      }
      free_block_unused(bn);

      blkno_bit_inbounds(jrnl);
      block_used := block_used[bn:=Some(ino)];
      txn.WriteBit(DataBitAddr(bn), true);

      assert Valid_jrnl_to_all() by {
        reveal_Valid_jrnl_to_block_used();
        reveal_Valid_jrnl_to_data_block();
        reveal_Valid_jrnl_to_inodes();
        DataBitAddr_disjoint(bn);
      }

      reveal_Valid_inodes_to_block_used();

      return;
    }

    // private
    // TODO: not used yet to reclaim blocks
    method zeroFrom(txn: Txn, ghost ino: Ino, i: Inode.Inode, blkoff: nat)
      returns (i': Inode.Inode)
      modifies Repr()
      requires Valid() ensures Valid()
      requires txn.jrnl == jrnl
      requires is_cur_inode(ino, i)
      requires |i.blks|-1 >= i.used_blocks
      requires blkoff < 15
      ensures is_cur_inode(ino, i')
      ensures i' == i.(blks := i.blks[blkoff := 0])
      ensures (
      var d0 := old(inode_blks[ino]);
      var d' := d0.(blks := d0.blks[blkoff := block0]);
      inode_blks == old(inode_blks[ino:=d'])
      )
    {
      var bn := i.blks[blkoff];
      if bn == 0 {
        i' := i;
        ghost var d0 := inode_blks[ino];
        assert d0.blks[blkoff] == block0 by {
          reveal_blks_match?();
        }
        assert d0.(blks := d0.blks[blkoff := block0]) == d0;
        return;
      }

      assert blkno_ok(bn) by {
        reveal_blks_match?();
      }

      balloc.Free(bn);

      blkno_bit_inbounds(jrnl);
      txn.WriteBit(DataBitAddr(bn), false);
      block_used := block_used[bn := None];

      assert Valid_jrnl_to_all() by {
        reveal_Valid_jrnl_to_block_used();
        reveal_Valid_jrnl_to_inodes();
        reveal_Valid_jrnl_to_data_block();
      }

      i' := i.(blks := i.blks[blkoff := 0]);
      assert i'.Valid() by {
        // TODO: use this syntax everywhere
        reveal Inode.blks_unique();
      }

      writeInode(ino, i');

      ghost var d0 := inode_blks[ino];
      inode_blks := inode_blks[ino := d0.(blks := d0.blks[blkoff := block0])];

      assert Valid_jrnl_to_all() by {
        reveal_Valid_jrnl_to_block_used();
        reveal_Valid_jrnl_to_inodes();
        reveal_Valid_jrnl_to_data_block();
      }

      assert Valid_data() by {
        reveal_blks_match?();
      }

      assert Valid_inodes() by {
        reveal_Valid_inodes_to_block_used();
        Inode.reveal_blks_unique();
        forall bn | bn in inodes[ino].blks && bn != 0
          ensures blkno_ok(bn)
          ensures block_used[bn] == Some(ino)
        {
          assert bn in old(inodes[ino].blks);
        }
      }
    }

    // public
    method allocateToInode(txn: Txn, ghost ino: Ino, i: Inode.Inode, blkoff: nat)
      returns (ok: bool, i': Inode.Inode, bn: Blkno)
      modifies Repr()
      requires Valid() ensures Valid()
      requires txn.jrnl == jrnl
      requires is_cur_inode(ino, i) ensures is_cur_inode(ino, i')
      requires blkoff < 15 && i.blks[blkoff] == 0
      // guarantees bn != 0
      ensures ok ==> is_alloc_bn(bn)
      ensures ok ==> inode_blks ==
        old(var d0 := inode_blks[ino];
            var d' := d0.(blks := d0.blks[blkoff:= data_block[bn]]);
            inode_blks[ino := d'])
      ensures !ok ==> inode_blks == old(inode_blks)
      ensures ok ==> i' == i.(blks := i.blks[blkoff := bn])
      ensures ok ==> old(block_used[bn].None?)
    {
      ok, bn := allocateTo(txn, ino, i);
      if !ok {
        i' := i;
        return;
      }
      ok := true;

      // this is the garbage data we're adding to the inode
      ghost var data := data_block[bn];

      i' := i.(blks := i.blks[blkoff := bn]);
      assert i'.Valid() by {
        Inode.blks_unique_extend(i.blks, blkoff, bn);
      }
      writeInode(ino, i');

      ghost var d0 := inode_blks[ino];
      ghost var d' := d0.(blks := d0.blks[blkoff := data]);
      inode_blks := inode_blks[ino := d'];

      assert inode_blks_match(i', d', data_block) by {
        reveal_blks_match?();
      }

      assert Valid_jrnl_to_all() by {
        reveal Valid_jrnl_to_inodes();
        reveal Valid_jrnl_to_block_used();
      }

      assert Valid() by {
        reveal Valid_inodes_to_block_used();
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

    // public
    method getInodeBlk(txn: Txn, ghost ino: Ino, i: Inode.Inode, blkoff: nat)
      returns (bs: Bytes)
      modifies {}
      requires Valid() ensures Valid()
      requires
      && this.jrnl == txn.jrnl
      && is_inode(ino, i)
      requires blkoff < 15
      ensures fresh(bs)
      ensures
      && is_block(bs.data)
      && bs.data == inode_blks[ino].blks[blkoff]
      // && blkno_ok(i.blks[blkoff])
      // && block_used[i.blks[blkoff]] == Some(ino)
    {
      var bn := i.blks[blkoff];
      reveal_blks_match?();
      if bn == 0 {
        bs := NewBytes(4096);
        return;
      }
      datablk_inbounds(jrnl, bn);
      bs := txn.Read(DataBlk(bn), 4096*8);
      reveal_Valid_inodes_to_block_used();
      reveal_Valid_jrnl_to_data_block();
    }

    lemma inode_sz_no_overflow(ino: Ino, i: Inode.Inode, delta: uint64)
      requires Valid()
      requires is_inode(ino, i)
      requires delta as nat <= 8192
      ensures no_overflow(i.sz as nat, delta as nat)
    {}

    // public
    // TODO: change this to zero a specified tail of the file
    method freeUnused(txn: Txn, ino: Ino, i: Inode.Inode) returns (i': Inode.Inode)
      modifies Repr()
      requires Valid()
      requires txn.jrnl == jrnl
      requires is_cur_inode(ino, i)
      ensures Valid()
      ensures is_cur_inode(ino, i')
      ensures inode_blks == old(inode_blks)
    {
      i' := i;
    }

  }
}
