include "../../util/marshal.i.dfy"
include "../../nonlin/roundup.dfy"

// NOTE: this module, unlike the others in this development, is not intended to
// be opened
module Inode {
  import opened Machine
  import opened Round
  import IntEncoding
  import opened Arith
  import opened Collections
  import opened ByteSlice
  import opened Marshal

  datatype Inode = Mk(sz: uint64, blks: seq<uint64>)
  {
    // how many blocks is the inode actually referencing with its size?
    const used_blocks: nat := div_roundup_alt(sz as nat, 4096)

    predicate Valid()
    {
      && ValidBlks(blks)
      && used_blocks <= |blks|
    }

    function method num_blks(): uint64
      requires Valid()
    {
      |blks| as uint64
    }

    function method {:opaque} used_blocks_u64(): (x:uint64)
      requires Valid()
      ensures x as nat == used_blocks
    {
      div_roundup64(sz, 4096)
    }

    lemma sz_bound()
      requires Valid()
      ensures sz as nat <= |blks|*4096 <= 15*4096
    {}
  }

  predicate {:opaque} blks_unique(blks: seq<uint64>)
  {
    unique(blks)
  }

  predicate ValidBlks(blks: seq<uint64>)
  {
    // only direct blocks that fit in the inode
    && |blks| <= 15
    && blks_unique(blks)
  }

  function inode_enc(i: Inode): seq<Encodable>
    requires i.Valid()
  {
    [EncUInt32(i.sz as uint32), EncUInt32(i.num_blks() as uint32)] + seq_fmap(encUInt64, i.blks)
  }

  lemma encode_len(i: Inode)
    requires i.Valid()
    ensures |seq_encode(inode_enc(i))| == 8*(1 + |i.blks|)
  {
    enc_uint64_len(i.blks);
  }

  function {:opaque} enc(i: Inode): (bs:seq<byte>)
    ensures |bs| == 128
  {
    if i.Valid() then
      (encode_len(i);
      assert |seq_encode(inode_enc(i))| == 8*(1+|i.blks|);
      seq_encode(inode_enc(i)) + repeat(0 as byte, 128-(8*(1+|i.blks|))))
    else repeat(0 as byte, 128)
  }

  const zero: Inode := Mk(0, []);

  lemma zero_valid()
    ensures zero.Valid()
  {
    reveal_blks_unique();
  }

  lemma zero_encoding()
    ensures zero.Valid()
    ensures repeat(0 as byte, 128) == enc(zero)
  {
    zero_valid();
    //assert inode_enc(zero) == [EncUInt64(0)];
    //assert repeat(0 as byte, 8) == [0,0,0,0,0,0,0,0];
    repeat_split(0 as byte, 128, 8, 128-8);
    IntEncoding.lemma_enc_0();
    IntEncoding.lemma_enc_32_0();
    reveal_enc();
  }

  method encode_ino(i: Inode) returns (bs:Bytes)
    modifies {}
    requires i.Valid()
    ensures fresh(bs)
    ensures bs.data == enc(i)
  {
    var e := new Encoder(128);
    e.PutInt32(i.sz as uint32);
    e.PutInt32(i.num_blks() as uint32);
    var k: uint64 := 0;
    while k < i.num_blks()
      modifies e.Repr
      invariant e.Valid()
      invariant 0 <= k <= i.num_blks()
      invariant e.bytes_left() == 128 - ((k as nat+1)*8)
      invariant e.enc ==
      [EncUInt32(i.sz as uint32), EncUInt32(i.num_blks() as uint32)] +
      seq_fmap(blkno => EncUInt64(blkno), i.blks[..k])
    {
      e.PutInt(i.blks[k as nat]);
      k := k + 1;
    }
    assert i.blks[..|i.blks|] == i.blks;
    assert e.enc == inode_enc(i);
    reveal_enc();
    bs := e.Finish();
  }

  method decode_ino(bs: Bytes, ghost i: Inode) returns (i': Inode)
    modifies {}
    requires bs.Valid()
    requires i.Valid()
    requires bs.data == enc(i)
    ensures i' == i
  {
    // note that we use nat throughout since we're mostly using Dafny operations
    // that require nats anyway and it's more efficient to stay with big
    // integers than convert back and forth
    reveal_enc();
    var dec := new Decoder.Init(bs, inode_enc(i));
    var sz: uint32 := dec.GetInt32(i.sz as uint32);
    var num_blks_ := dec.GetInt32(i.num_blks() as uint32);
    var num_blks: nat := num_blks_ as nat;
    assert num_blks == |i.blks|;
    assert dec.enc == seq_fmap(blkno => EncUInt64(blkno), i.blks);

    var blks: array<uint64> := new uint64[num_blks];

    var k: nat := 0;
    while k < num_blks
      modifies dec, blks
      invariant dec.Valid()
      invariant i.Valid()
      invariant 0 <= k <= num_blks
      invariant blks.Length == num_blks;
      invariant blks[..k] == i.blks[..k]
      invariant dec.enc == seq_fmap(blkno => EncUInt64(blkno), i.blks[k..])
    {
      var blk := dec.GetInt(i.blks[k]);
      blks[k] := blk;
      k := k + 1;
    }
    assert blks[..num_blks] == blks[..];
    return Mk(sz as uint64, blks[..]);
  }
}
