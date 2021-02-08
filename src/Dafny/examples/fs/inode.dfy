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
      ensures sz as nat <= |blks|*4096 <= 14*4096
    {}
  }

  predicate {:opaque} blks_unique(blks: seq<uint64>)
  {
    unique(blks)
  }

  predicate ValidBlks(blks: seq<uint64>)
  {
    // only direct blocks that fit in the inode
    && |blks| <= 14
    && blks_unique(blks)
  }

  function inode_enc(i: Inode): seq<Encodable>
    requires i.Valid()
  {
    [EncUInt64(i.sz), EncUInt64(i.num_blks())] + seq_fmap(blkno => EncUInt64(blkno), i.blks)
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

  lemma encode_len(i: Inode)
    requires i.Valid()
    // this doesn't verify in Emacs for unclear reasons
    ensures |seq_encode(inode_enc(i))| == 8*(2 + |i.blks|)
  {
    enc_uint64_len(i.blks);
    var e1 := EncUInt64(i.sz);
    var e2 := EncUInt64(i.num_blks());
    calc {
      |seq_encode(inode_enc(i))|;
      |enc_encode(e1) + enc_encode(e2) + seq_enc_uint64(i.blks)|;
      8 + 8 + 8*|i.blks|;
    }
  }

  function {:opaque} enc(i: Inode): (bs:seq<byte>)
    ensures |bs| == 128
  {
    if i.Valid() then
      (encode_len(i);
      assert |seq_encode(inode_enc(i))| == 8*(2+|i.blks|);
      seq_encode(inode_enc(i)) + repeat(0 as byte, 128-(8*(2+|i.blks|))))
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
    reveal_enc();
  }

  method encode_ino(i: Inode) returns (bs:Bytes)
    modifies {}
    requires i.Valid()
    ensures fresh(bs)
    ensures bs.data == enc(i)
  {
    var e := new Encoder(128);
    e.PutInt(i.sz);
    e.PutInt(i.num_blks());
    var k: uint64 := 0;
    while k < i.num_blks()
      modifies e.Repr
      invariant e.Valid()
      invariant 0 <= k <= i.num_blks()
      invariant e.bytes_left() == 128 - ((k as nat+2)*8)
      invariant e.enc ==
      [EncUInt64(i.sz), EncUInt64(i.num_blks())] +
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
    var sz := dec.GetInt(i.sz);
    var num_blks_ := dec.GetInt(i.num_blks());
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
    return Mk(sz, blks[..]);
  }
}
