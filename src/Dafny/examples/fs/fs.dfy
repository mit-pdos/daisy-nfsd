include "../../util/marshal.i.dfy"
include "../../jrnl/jrnl.s.dfy"

// NOTE: this module, unlike the others in this development, is not intended to
// be opened
//
// NOTE: factoring out Inode to a separate file made this file much _slower_ for
// some reason
module Inode {
  import opened Machine
  import IntEncoding
  import opened Collections
  import opened ByteSlice
  import opened Marshal

  datatype Inode = Mk(sz: uint64, blks: seq<uint64>)

  function method div_roundup(x: nat, k: nat): nat
    requires k >= 1
  {
    (x + (k-1)) / k
  }

  predicate Valid(i:Inode)
  {
    var blks_ := i.blks;
    // only direct blocks
    && |blks_| == 15
    && i.sz as nat <= |blks_| * 4096
    && unique(blks_[..div_roundup(i.sz as nat, 4096)])
  }

  function inode_enc(i: Inode): seq<Encodable>
  {
    [EncUInt64(i.sz)] + seq_fmap(blkno => EncUInt64(blkno), i.blks)
  }

  function enc(i: Inode): seq<byte>
  {
    seq_encode(inode_enc(i))
  }

  const zero: Inode := Mk(0, repeat(0 as uint64, 15));

  lemma zero_valid()
    ensures Valid(zero)
  {}

  lemma {:induction count} repeat_zero_ints(count: nat)
    ensures seq_encode(repeat(EncUInt64(0), count)) == repeat(0 as byte, 8*count)
  {
    var z := EncUInt64(0);
    if count == 0 {
      reveal_repeat();
      assert 8*count == 0;
      assert repeat(z, count) == [];
      //assert seq_encode([]) == [];
      assert repeat(0 as byte, 8*count) == [];
    } else {
      IntEncoding.lemma_enc_0();
      assert repeat(0 as byte, 8) == enc_encode(z);
      repeat_split(0 as byte, 8*count, 8, 8*(count-1));
      repeat_zero_ints(count-1);
      assert repeat(z, count) == [z] + repeat(z, count-1);
      //assert seq_encode(repeat(z, count)) == repeat(0 as byte, 8) + repeat(0 as byte, 8*(count-1));
      //assert seq_encode([z]) == repeat(0 as byte, 8);
    }
  }

  lemma zero_encoding()
    ensures Valid(zero)
    ensures repeat(0 as byte, 128) == enc(zero)
  {
    zero_valid();
    assert inode_enc(zero) == [EncUInt64(0)] + repeat(EncUInt64(0), 15);
    assert inode_enc(zero) == repeat(EncUInt64(0), 16);
    repeat_zero_ints(16);
  }

  method encode_ino(i: Inode) returns (bs:Bytes)
    modifies {}
    requires Valid(i)
    ensures fresh(bs)
    ensures bs.data == enc(i)
  {
    var enc := new Encoder(128);
    enc.PutInt(i.sz);
    var k: nat := 0;
    while k < 15
      modifies enc.Repr
      invariant enc.Valid()
      invariant 0 <= k <= 15
      invariant enc.bytes_left() == 128 - ((k+1)*8)
      invariant enc.enc ==
      [EncUInt64(i.sz)] +
      seq_fmap(blkno => EncUInt64(blkno), i.blks[..k])
    {
      enc.PutInt(i.blks[k]);
      k := k + 1;
    }
    assert i.blks[..15] == i.blks;
    bs := enc.FinishComplete();
  }

  method decode_ino(bs: Bytes, ghost i: Inode) returns (i': Inode)
    modifies {}
    requires bs.Valid()
    requires Valid(i)
    requires bs.data == enc(i)
    ensures i' == i
  {
    var dec := new Decoder();
    dec.Init(bs, inode_enc(i));
    var sz := dec.GetInt(i.sz);
    assert dec.enc == seq_fmap(blkno => EncUInt64(blkno), i.blks);

    var blks: seq<uint64> := [];

    var k: nat := 0;
    while k < 15
      modifies dec
      invariant dec.Valid()
      invariant Valid(i)
      invariant 0 <= k <= 15
      invariant blks == i.blks[..k]
      invariant dec.enc == seq_fmap(blkno => EncUInt64(blkno), i.blks[k..])
    {
      var blk := dec.GetInt(i.blks[k]);
      blks := blks + [blk];
      k := k + 1;
    }
    return Mk(sz, blks);
  }
}

module Fs {
  import Inode
  import opened Machine
  import opened ByteSlice
  import opened JrnlSpec
  import opened Kinds
  import opened Marshal

  type Ino = uint64

  predicate blkno_ok(blkno: Blkno) { blkno < 4096*8 }
  predicate ino_ok(ino: Blkno) { ino < 32 }

  // disk layout, in blocks:
  //
  // 513 for the jrnl
  // 1 inode block (32 inodes)
  // 1 bitmap block
  // 4096*8 data blocks
  const NumBlocks: nat := 513 + 1 + 1 + 4096*8
    // if you want to make a disk for the fs 40,000 blocks is a usable number
  lemma NumBlocks_upper_bound()
    ensures NumBlocks < 40_000
  {}

  const InodeBlk: Blkno := 513
  const DataAllocBlk: Blkno := 514

  function method InodeAddr(ino: Ino): (a:Addr)
    requires ino_ok(ino)
    ensures a.off < 4096*8
  {
    Addr(InodeBlk, ino*128*8)
  }
  function method DataBitAddr(bn: uint64): Addr
    requires blkno_ok(bn)
  {
    Addr(DataAllocBlk, bn)
  }
  function method DataBlk(bn: uint64): Addr
    requires blkno_ok(bn)
  {
    Addr(513+2+bn, 0)
  }

  const fs_kinds: map<Blkno, Kind> :=
    // NOTE(tej): trigger annotation suppresses warning (there's nothing to
    // trigger on here, but also nothing is necessary)
    map blkno: Blkno {:trigger} |
      513 <= blkno as nat < NumBlocks
      :: (if blkno == InodeBlk
      then KindInode
      else if blkno == DataAllocBlk
        then KindBit
        else KindBlock) as Kind

  lemma fs_kinds_valid()
    ensures kindsValid(fs_kinds)
  {}

  datatype Option<T> = Some(x:T) | None

  class Filesys
  {

    // spec state
    ghost var data: map<Ino, seq<byte>>;

    // intermediate abstractions
    ghost var inodes: map<Ino, Inode.Inode>;
    // gives the inode that owns the block
    ghost var block_used: map<Blkno, Option<Ino>>;
    ghost var data_block: map<Blkno, seq<byte>>;

    var jrnl: Jrnl;

    predicate Valid_basics()
      reads this, jrnl
    {
      && jrnl.Valid()
      && jrnl.kinds == fs_kinds
    }

    static lemma blkno_bit_inbounds(jrnl: Jrnl)
      requires jrnl.Valid()
      requires jrnl.kinds == fs_kinds
      ensures forall bn :: blkno_ok(bn) ==> DataBitAddr(bn) in jrnl.data
    {}

    static lemma inode_inbounds(jrnl: Jrnl)
      requires jrnl.Valid()
      requires jrnl.kinds == fs_kinds
      ensures forall ino :: ino_ok(ino) ==> InodeAddr(ino) in jrnl.data
    {}

    predicate Valid_block_used()
      requires Valid_basics()
      reads this, jrnl
    {
      blkno_bit_inbounds(jrnl);
      && (forall bn :: blkno_ok(bn) ==> bn in block_used)
      && (forall bn | bn in block_used ::
        && blkno_ok(bn)
        && jrnl.data[DataBitAddr(bn)] == ObjBit(block_used[bn].Some?))
    }

    predicate Valid_data_block()
      requires Valid_basics()
      reads this, jrnl
    {
      && (forall bn :: blkno_ok(bn) ==> bn in data_block)
      && (forall bn | bn in data_block ::
        && blkno_ok(bn)
        && jrnl.data[DataBlk(bn)] == ObjData(data_block[bn]))
    }

    predicate Valid_inodes()
      requires Valid_basics()
      reads this, jrnl
    {
      inode_inbounds(jrnl);
      && (forall ino: Ino | ino_ok(ino) :: ino in inodes)
      && (forall ino: Ino | ino in inodes ::
        && ino_ok(ino)
        && Inode.Valid(inodes[ino])
        && jrnl.data[InodeAddr(ino)] == ObjData(Inode.enc(inodes[ino])))
    }

    predicate Valid()
      reads this, jrnl
    {
      // TODO: split this into multiple predicates, ideally opaque
      && Valid_basics()

      // NOTE(tej): this is for the real abstract state, which we're not worrying
      // about for now
      // && (forall ino: Ino | ino in data :: ino in inodes)
      // && (forall ino: Ino | ino in inodes ::
      //   && ino in data
      //   && inodes[ino].sz as nat == |data[ino]|)
      // TODO: tie Inode.Inode low-level value + block data to abstract state

      && this.Valid_block_used()
      && this.Valid_data_block()
      && this.Valid_inodes()

      // TODO: tie inode ownership to inode block lists
    }

    constructor(d: Disk)
      ensures Valid()
    {
      // FIXME: using constructor directly since it has a model, but for
      // compilation need to use // NewJrnl
      var jrnl := new Jrnl(fs_kinds);
      this.jrnl := jrnl;

      this.inodes := map ino: Ino | ino < 513 :: Inode.zero;
      Inode.zero_encoding();
      this.block_used := map bn: uint64 |
        blkno_ok(bn) :: None;
      this.data_block := map bn: uint64 |
        blkno_ok(bn) :: zeroObject(KindBlock).bs;
      new;
      assert Valid_inodes();
      assert 32 in inodes;
      assert ino_ok(32);
      assert false;
    }
  }

}
