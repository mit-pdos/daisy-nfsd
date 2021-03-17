include "../../util/marshal.i.dfy"
include "../../nonlin/roundup.dfy"

// NOTE: this module, unlike the others in this development, is not intended to
// be opened
module Inode {
  import opened Machine
  import opened Round
  import IntEncoding
  import opened Arith
  import opened ByteSlice
  import opened Marshal
  import C = Collections

  const MAX_SZ_u64: uint64 := 4096 * (10 + 3*512 + 512*512*512);
  const MAX_SZ: nat := MAX_SZ_u64 as nat;

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

    function enc(): seq<byte>
    {
      IntEncoding.le_enc64(to_u64())
    }

    lemma enc_dec()
      ensures from_u64(IntEncoding.le_dec64(this.enc())) == this
    {
      IntEncoding.lemma_le_enc_dec64(to_u64());
      from_to_u64();
    }
  }

  datatype NfsTime = NfsTime(sec: uint32, nsec: uint32)
  {
    static const zero: NfsTime := NfsTime(0, 0)
  }

  datatype Attrs = Attrs(mode: uint32, atime: NfsTime, mtime: NfsTime)
  {
    static const zero: Attrs := Attrs(0, NfsTime.zero, NfsTime.zero)
  }

  datatype Meta = Meta(sz: uint64, ty: InodeType)
  {
    function enc(): seq<byte>
    {
      IntEncoding.le_enc64(sz) + ty.enc()
    }
  }

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
  type Inode = x:preInode | x.Valid() ghost witness preInode.preZero

  const zero: Inode := preInode.preZero

  lemma zero_encoding()
    ensures C.repeat(0 as byte, 128) == enc(zero)
  {
    IntEncoding.lemma_enc_0();
    zero_encode_seq_uint64(14);
    reveal enc();
  }

  function {:opaque} enc(i: Inode): (bs:seq<byte>)
    ensures |bs| == 128
  {
    assert i.Valid();
    var blk_enc := seq_enc_uint64(i.blks);
    enc_uint64_len(i.blks);
    i.meta.enc() + blk_enc
  }

  lemma enc_app(i: Inode)
    ensures enc(i) ==
    (IntEncoding.le_enc64(i.meta.sz) + i.meta.ty.enc()) +
    seq_enc_uint64(i.blks)
  {
    reveal enc();
  }
}
