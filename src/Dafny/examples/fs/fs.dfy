include "../../util/marshal.i.dfy"
include "../../jrnl/jrnl.s.dfy"

// NOTE: this module, unlike the others in this development, is not intended to
// be opened
//
// NOTE: factoring out Inode to a separate file made this file much _slower_ for
// some reason
module Inode {
  import opened Machine
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

  lemma zero_encoding()
    ensures Valid(zero)
    ensures repeat(0 as byte, 128) == enc(zero)
  {
    assert inode_enc(zero) == [EncUInt64(0)] + repeat(EncUInt64(0), 15);
    assert inode_enc(zero) == repeat(EncUInt64(0), 16);
    // TODO: need to assume this about little-endian encoding
    assume enc_encode(EncUInt64(0)) == repeat(0 as byte, 8);
    // TODO: prove this eventually
    assume false;
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

  // disk layout, in blocks:
  //
  // 513 for the jrnl
  // 1 inode block (32 inodes)
  // 1 bitmap block
  // 4096*8 data blocks
  const NumBlocks: nat := 513 + 1 + 1 + 4096*8

  const InodeBlk: Blkno := 513
  const DataAllocBlk: Blkno := 514
  function method DataBlk(blkno: uint64): Addr
    requires blkno as nat < 4096*8
  {
    Addr(513+2+blkno, 0)
  }
  function method InodeAddr(ino: Ino): (a:Addr)
    requires ino < 32
    ensures a.off < 4096*8
  {
    Addr(InodeBlk, ino*128*8)
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

  class Filesys
  {

    // spec state
    ghost var data: map<Ino, seq<byte>>;

    // intermediate abstractions
    ghost var inodes: map<Ino, Inode.Inode>;
    ghost var block_used: map<Blkno, bool>;
    ghost var data_block: map<Blkno, seq<byte>>;

    var jrnl: Jrnl;
    var balloc: Allocator;

    static predicate ValidState(jrnl: Jrnl, data: map<Ino, seq<byte>>)
      reads jrnl
    {
      && jrnl.Valid()
      // TODO: eventually everything in Valid should go here (but this is
      // annoying because we're going to be adding several ghost fields to Filesys)
    }

    predicate Valid()
      reads this, jrnl
    {
      && ValidState(jrnl, data)
      && jrnl.kinds == fs_kinds
      && (forall ino: Ino | ino < 32 ::
        && ino in inodes
        && Inode.Valid(inodes[ino]))
      && (forall ino: Ino | ino in data :: ino in inodes)
      && (forall ino: Ino | ino in inodes ::
        && ino in data
        && inodes[ino].sz as nat == |data[ino]|)

      && (forall blkno: uint64 :: blkno < 4096*8 <==> blkno in block_used)
      && (forall blkno | blkno in block_used ::
         jrnl.data[Addr(DataAllocBlk, blkno)] == ObjBit(block_used[blkno]))
      // this is true but probably not useful
      // && (forall blkno | blkno in block_used ::
      //    jrnl.size(Addr(DataAllocBlk, blkno)) == 1)
      && (forall blkno :: blkno in data_block <==> blkno < 4096*8)
      && (forall blkno | blkno in data_block :: jrnl.data[DataBlk(blkno)] == ObjData(data_block[blkno]))

      && (forall ino: Ino | ino < 32 :: jrnl.data[InodeAddr(ino)] == ObjData(Inode.enc(inodes[ino])))

      && balloc.max == 4096*8
    }

    constructor(d: Disk)
      ensures Valid()
      ensures forall ino :: ino in this.data <==> ino < 513
      ensures forall ino | ino in data :: data[ino] == []
    {
      var jrnl := NewJrnl(d, fs_kinds);
      this.jrnl := jrnl;

      var balloc := NewAllocator(4096*8);
      balloc.MarkUsed(0);
      this.balloc := balloc;
      this.data := map ino: Ino {:trigger} | ino < 513 :: [];

      this.inodes := map ino: Ino {:trigger} | ino < 513 :: Inode.zero;
      Inode.zero_encoding();
      this.block_used := map blkno: uint64 {:trigger} |
        blkno < 4096*8 :: false;
      this.data_block := map blkno: uint64 |
        blkno < 4096*8 :: zeroObject(KindBlock).bs;
    }
  }

}
