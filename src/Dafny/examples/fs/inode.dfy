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

  const MAX_SZ: nat := 10 + 4*512 + 512*512*512;
  const MAX_SZ_u64: uint64 := MAX_SZ as uint64;

  datatype preInode = Mk(sz: uint64, blks: seq<uint64>)
  {

    // how many blocks is the inode actually referencing with its size?
    const used_blocks: nat := div_roundup_alt(sz as nat, 4096)

    predicate Valid()
    {
      && ValidBlks(blks)
      && sz as nat <= MAX_SZ
    }

    function method {:opaque} used_blocks_u64(): (x:uint64)
      requires Valid()
      ensures x as nat == used_blocks
    {
      div_roundup64(sz, 4096)
    }
  }
  type Inode = x:preInode | x.Valid() witness Mk(0, C.repeat(0 as uint64, 15))

  predicate ValidBlks(blks: seq<uint64>)
  {
    && |blks| == 15
  }

  function inode_enc(i: Inode): seq<Encodable>
  {
    [EncUInt64(i.sz)] + seq_fmap(encUInt64, i.blks)
  }

  lemma encode_len(i: Inode)
    ensures |seq_encode(inode_enc(i))| == 128
  {
    enc_uint64_len(i.blks);
  }

  function {:opaque} enc(i: Inode): (bs:seq<byte>)
    ensures |bs| == 128
  {
    encode_len(i);
    assert |seq_encode(inode_enc(i))| == 128;
    seq_encode(inode_enc(i))
  }

  const zero: Inode := Mk(0, repeat(0 as uint64, 15));

  lemma zero_encoding()
    ensures repeat(0 as byte, 128) == enc(zero)
  {
    assert inode_enc(zero) == [EncUInt64(0)] + repeat(EncUInt64(0), 15);
    IntEncoding.lemma_enc_0();
    zero_encode_seq_uint64(15);
    reveal_enc();
  }

  method encode_ino(i: Inode) returns (bs:Bytes)
    modifies {}
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
