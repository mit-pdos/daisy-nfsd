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

  const MAX_SZ: nat := 15*4096;
  const MAX_SZ_u64: uint64 := MAX_SZ as uint64;

  datatype Inode = Mk(sz: uint64, blks: seq<uint64>)
  {

    // how many blocks is the inode actually referencing with its size?
    const used_blocks: nat := div_roundup_alt(sz as nat, 4096)

    predicate Valid()
    {
      && ValidBlks(blks)
      && sz as nat <= MAX_SZ
    }

    function method num_blks(): uint64
    {
      15
    }

    function method {:opaque} used_blocks_u64(): (x:uint64)
      requires Valid()
      ensures x as nat == used_blocks
    {
      div_roundup64(sz, 4096)
    }
  }

  predicate {:opaque} blks_unique(blks: seq<uint64>)
  {
    forall i, j | 0 <= i < |blks| && 0 <= j < |blks| ::
      blks[i] == blks[j] ==> i == j || blks[i] == 0
  }

  lemma blks_unique_extend(blks: seq<uint64>, blkoff: nat, bn: uint64)
    requires blkoff < |blks|
    requires blks_unique(blks)
    requires bn != 0 && bn !in blks
    ensures blks_unique(blks[blkoff := bn])
  {
    reveal_blks_unique();
  }

  predicate ValidBlks(blks: seq<uint64>)
  {
    && |blks| == 15
    && blks_unique(blks)
  }

  function inode_enc(i: Inode): seq<Encodable>
    requires i.Valid()
  {
    [EncUInt64(i.sz)] + seq_fmap(encUInt64, i.blks)
  }

  lemma encode_len(i: Inode)
    requires i.Valid()
    ensures |seq_encode(inode_enc(i))| == 128
  {
    enc_uint64_len(i.blks);
  }

  function {:opaque} enc(i: Inode): (bs:seq<byte>)
    ensures |bs| == 128
  {
    if i.Valid() then
      (encode_len(i);
      assert |seq_encode(inode_enc(i))| == 128;
      seq_encode(inode_enc(i)))
    else repeat(0 as byte, 128)
  }

  const zero: Inode := Mk(0, repeat(0 as uint64, 15));

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
    assert inode_enc(zero) == [EncUInt64(0)] + repeat(EncUInt64(0), 15);
    IntEncoding.lemma_enc_0();
    zero_encode_seq_uint64(15);
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
    e.PutInts(i.blks);
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
    reveal_enc();
    var dec := new Decoder.Init(bs, inode_enc(i));
    var sz := dec.GetInt(i.sz);
    var blks := dec.GetInts(15, i.blks);
    return Mk(sz as uint64, blks);
  }
}
