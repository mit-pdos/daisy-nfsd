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

  predicate {:opaque} blks_unique(blks: seq<uint64>)
  {
    unique(blks)
  }

  predicate ValidBlks(blks: seq<uint64>)
  {
    && |blks| <= 15
    && blks_unique(blks)
  }

  predicate Valid(i:Inode)
  {
    && ValidBlks(i.blks)
    // only direct blocks
    && |i.blks| == div_roundup_alt(i.sz as nat, 4096)
  }

  lemma Valid_sz_bound(i:Inode)
    requires ValidBlks(i.blks)
    requires |i.blks| == div_roundup_alt(i.sz as nat, 4096)
    ensures i.sz as nat <= |i.blks|*4096 <= 15*4096
  {}

  function inode_enc(i: Inode): seq<Encodable>
  {
    [EncUInt64(i.sz)] + seq_fmap(blkno => EncUInt64(blkno), i.blks)
  }

  function seq_enc_uint64(xs: seq<uint64>): seq<byte>
  {
    seq_encode(seq_fmap(blkno => EncUInt64(blkno), xs))
  }

  lemma seq_enc_uint64_unfold(xs: seq<uint64>)
    requires 0 < |xs|
    ensures seq_enc_uint64(xs) == IntEncoding.le_enc64(xs[0]) + seq_enc_uint64(xs[1..])
  {}

  lemma {:induction xs} enc_uint64_len(xs: seq<uint64>)
    decreases xs
    ensures |seq_enc_uint64(xs)| == 8*|xs|
  {
    if xs == [] {}
    else {
      seq_enc_uint64_unfold(xs);
      enc_uint64_len(xs[1..]);
      Arith.mul_distr_sub_l(8, |xs|, 1);
      assert 8*|xs[1..]| == 8*|xs| - 8;
    }
  }

  function enc(i: Inode): (bs:seq<byte>)
    ensures |bs| == 128
  {
    if Valid(i) then
      (enc_uint64_len(i.blks);
      assert |seq_encode(inode_enc(i))| == 8+8*|i.blks|;
      seq_encode(inode_enc(i)) + repeat(0 as byte, 128-(8+8*|i.blks|)))
    else repeat(0 as byte, 128)
  }

  const zero: Inode := Mk(0, []);

  lemma zero_valid()
    ensures Valid(zero)
  {
    reveal_blks_unique();
  }

  lemma zero_encoding()
    ensures Valid(zero)
    ensures repeat(0 as byte, 128) == enc(zero)
  {
    zero_valid();
    //assert inode_enc(zero) == [EncUInt64(0)];
    //assert repeat(0 as byte, 8) == [0,0,0,0,0,0,0,0];
    repeat_split(0 as byte, 128, 8, 128-8);
    IntEncoding.lemma_enc_0();
  }

  method encode_ino(i: Inode) returns (bs:Bytes)
    modifies {}
    requires Valid(i)
    ensures fresh(bs)
    ensures bs.data == enc(i)
  {
    var e := new Encoder(128);
    e.PutInt(i.sz);
    var num_blocks: uint64 := div_roundup64(i.sz, 4096);
    assert num_blocks as nat == |i.blks|;
    var k: uint64 := 0;
    while k < num_blocks
      modifies e.Repr
      invariant e.Valid()
      invariant 0 <= k <= num_blocks
      invariant e.bytes_left() == 128 - ((k as nat+1)*8)
      invariant e.enc ==
      [EncUInt64(i.sz)] +
      seq_fmap(blkno => EncUInt64(blkno), i.blks[..k])
    {
      e.PutInt(i.blks[k as nat]);
      k := k + 1;
    }
    assert i.blks[..|i.blks|] == i.blks;
    assert e.enc == inode_enc(i);
    bs := e.Finish();
  }

  method decode_ino(bs: Bytes, ghost i: Inode) returns (i': Inode)
    modifies {}
    requires bs.Valid()
    requires Valid(i)
    requires bs.data == enc(i)
    ensures i' == i
  {
    // note that we use nat throughout since we're mostly using Dafny operations
    // that require nats anyway and it's more efficient to stay with big
    // integers than convert back and forth
    var dec := new Decoder();
    dec.Init(bs, inode_enc(i));
    var sz := dec.GetInt(i.sz);
    var num_blks: nat := div_roundup64(sz, 4096) as nat;
    assert num_blks == |i.blks|;
    assert dec.enc == seq_fmap(blkno => EncUInt64(blkno), i.blks);

    var blks: array<uint64> := new uint64[num_blks];

    var k: nat := 0;
    while k < num_blks
      modifies dec, blks
      invariant dec.Valid()
      invariant Valid(i)
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
    return Mk(sz, blks[..]);
  }
}
