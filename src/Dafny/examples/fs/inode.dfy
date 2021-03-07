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

  const MAX_SZ: nat := 4096 * (10 + 3*512 + 512*512*512);
  const MAX_SZ_u64: uint64 := MAX_SZ as uint64;

  datatype InodeType = InvalidType | FileType | DirType
  {
    function method to_u64(): uint64
    {
      match this {
        case InvalidType => 0
        case FileType => 1
        case DirType => 2
      }
    }

    static function method from_u64(x: uint64): InodeType
    {
      if x == 0 then InvalidType else if x == 1 then FileType else DirType
    }

    lemma from_to_u64()
      ensures from_u64(to_u64()) == this
    {}
  }

  datatype Meta = Meta(sz: uint64, ty: InodeType)

  datatype preInode = Mk(meta: Meta, blks: seq<uint64>)
  {
    const sz: uint64 := meta.sz
    const ty: InodeType := meta.ty

    static const preZero: preInode := Mk(Meta(0, InvalidType), C.repeat(0 as uint64, 14))

    predicate Valid()
    {
      && |blks| == 14
      && sz as nat <= MAX_SZ
    }
  }
  // NOTE(tej): we specifically don't provide a witness for performance reasons:
  // if there is a witness, the generated code starts every function that
  // returns an Inode by instantiating it with the witness, and this requires
  // allocating and filling a seq.
  type Inode = x:preInode | x.Valid() witness *

  const zero: Inode := preInode.preZero

  lemma zero_encoding()
    ensures repeat(0 as byte, 128) == enc(zero)
  {
    assert inode_enc(zero) == [EncUInt64(0), EncUInt64(0)] + repeat(EncUInt64(0), 14);
    IntEncoding.lemma_enc_0();
    zero_encode_seq_uint64(15);
    reveal_enc();
  }

  function inode_enc(i: Inode): seq<Encodable>
  {
    [EncUInt64(i.sz), EncUInt64(i.meta.ty.to_u64())] + seq_fmap(encUInt64, i.blks)
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

  method encode_ino(i: Inode) returns (bs:Bytes)
    modifies {}
    ensures fresh(bs)
    ensures bs.data == enc(i)
  {
    var e := new Encoder(128);
    e.PutInt(i.sz);
    e.PutInt(i.meta.ty.to_u64());
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
    var ty_u64 := dec.GetInt(i.meta.ty.to_u64());
    i.meta.ty.from_to_u64();
    var ty := InodeType.from_u64(ty_u64);
    var blks := dec.GetInts(14, i.blks);
    return Mk(Meta(sz as uint64, ty), blks);
  }
}
