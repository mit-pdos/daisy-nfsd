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

  const MAX_SZ_u64: uint64 := 4096 * (8 + 2*512 + 512*512 + 512*512*512)
  const MAX_SZ: nat := MAX_SZ_u64 as nat

  datatype InodeType = InvalidType | FileType | DirType
  {
    function to_u32(): uint32
    {
      match this {
        case InvalidType => 0
        case FileType => 1
        case DirType => 2
      }
    }

    static function from_u32(x: uint32): InodeType
    {
      if x == 0 then InvalidType else if x == 1 then FileType else DirType
    }

    lemma from_to_u32()
      ensures from_u32(to_u32()) == this
    {}

    ghost function enc(): seq<byte>
    {
      IntEncoding.le_enc32(to_u32())
    }

    lemma enc_dec()
      ensures from_u32(IntEncoding.le_dec32(this.enc())) == this
    {
      IntEncoding.lemma_le_enc_dec32(to_u32());
      from_to_u32();
    }
  }

  datatype NfsTime = NfsTime(sec: uint32, nsec: uint32)
  {
    static const zero: NfsTime := NfsTime(0, 0)

    ghost function enc(): seq<byte>
    {
      IntEncoding.le_enc32(sec) + IntEncoding.le_enc32(nsec)
    }

    static lemma enc_zero()
      ensures C.repeat(0 as byte, 8) == zero.enc()
    {
      IntEncoding.lemma_enc_32_0();
    }

    static method decode(bs: Bytes, off: uint64, ghost t: NfsTime)
      returns (t': NfsTime)
      requires bs.Valid()
      requires off as nat + 8 <= |bs.data|
      requires bs.data[off .. off + 8] == t.enc()
      ensures t' == t
    {
      var sec := IntEncoding.UInt32Get(bs, off);
      var nsec := IntEncoding.UInt32Get(bs, off + 4);
      assert bs.data[off..off+4] == t.enc()[..4];
      assert bs.data[off+4..off+8] == t.enc()[4..];
      IntEncoding.lemma_le_enc_dec32(t.sec);
      IntEncoding.lemma_le_enc_dec32(t.nsec);
      return NfsTime(sec, nsec);
    }

    method put(off: uint64, bs: Bytes)
      modifies bs
      requires bs.Valid()
      requires off as nat + 8 <= |bs.data|
      ensures bs.data == old(C.splice(bs.data, off as nat, enc()))
    {
      IntEncoding.UInt32Put(sec, off, bs);
      IntEncoding.UInt32Put(nsec, off + 4, bs);
    }
  }

  datatype Attrs = Attrs(ty: InodeType, mode: uint32, uid: uint32, gid: uint32, mtime: NfsTime)
  {
    static const zero: Attrs := Attrs(InvalidType, 0, 0, 0, NfsTime.zero)
    static const zero_file: Attrs := Attrs(FileType, 0, 0, 0, NfsTime.zero)
    static const zero_dir: Attrs := Attrs(DirType, 0, 0, 0, NfsTime.zero)

    ghost function enc(): seq<byte>
    {
      IntEncoding.le_enc32(ty.to_u32()) +
        IntEncoding.le_enc32(mode) +
        IntEncoding.le_enc32(uid) +
        IntEncoding.le_enc32(gid) +
        mtime.enc()
    }

    lemma enc_len()
      ensures |enc()| == 24 // 4+4 + 4+4 + 8
    {}

    static lemma enc_zero()
      ensures C.repeat(0 as byte, 24) == zero.enc()
    {
      IntEncoding.lemma_enc_32_0();
      NfsTime.enc_zero();
    }

    static method decode(bs: Bytes, off: uint64, ghost attrs: Attrs)
      returns (attrs': Attrs)
      requires bs.Valid()
      requires off as nat + 24 <= |bs.data|
      requires bs.data[off .. off + 24] == attrs.enc()
      ensures attrs' == attrs
    {
      assert bs.data[off..off+4] == attrs.enc()[..4] by {
        C.double_subslice_auto(bs.data);
      }
      var ty_u32 := Marshal.UInt32Decode(bs, off, attrs.ty.to_u32());
      var ty := InodeType.from_u32(ty_u32);
      assert bs.data[off+4..off+8] == attrs.enc()[4..8] by {
        C.double_subslice_auto(bs.data);
      }
      var mode := Marshal.UInt32Decode(bs, off + 4, attrs.mode);

      assert bs.data[off + 8 .. off + 8+4] == attrs.enc()[8..12] by {
        C.double_subslice_auto(bs.data);
      }
      var uid := Marshal.UInt32Decode(bs, off + 8, attrs.uid);

      assert bs.data[off + 12 .. off + 12+4] == attrs.enc()[12..16] by {
        C.double_subslice_auto(bs.data);
      }
      var gid := Marshal.UInt32Decode(bs, off + 12, attrs.gid);
      assert bs.data[off + 16 .. off + 16+8] == attrs.enc()[16..24] by {
        C.double_subslice_auto(bs.data);
      }
      var mtime := NfsTime.decode(bs, off + 4+4+8, attrs.mtime);
      return Attrs(ty, mode, uid, gid, mtime);
    }

    method put(off: uint64, bs: Bytes)
      modifies bs
      requires bs.Valid()
      requires off as nat + 24 <= |bs.data|
      ensures bs.data == old(C.splice(bs.data, off as nat, enc()))
    {
      IntEncoding.UInt32Put(ty.to_u32(), off, bs);
      IntEncoding.UInt32Put(mode, off + 4, bs);
      IntEncoding.UInt32Put(uid, off + 4 + 4, bs);
      IntEncoding.UInt32Put(gid, off + 4 + 4 + 4, bs);
      mtime.put(off + 4 + 4 + 8, bs);
      assert bs.data[off as nat..off as nat+|enc()|] == enc();
      assert bs.data[..off as nat] == old(bs.data[..off as nat]);
    }
  }

  datatype Meta = Meta(sz: uint64, attrs: Attrs)
  {
    const ty := attrs.ty
    static const zero: Meta := Meta(0, Attrs.zero)

    ghost function enc(): seq<byte>
    {
      IntEncoding.le_enc64(sz) + attrs.enc()
    }

    lemma enc_len()
      ensures |enc()| == 32 // 8 + 24
    {}

    method put(off: uint64, bs: Bytes)
      modifies bs
      requires bs.Valid()
      requires off as nat + 32 <= |bs.data|
      ensures bs.data == old(C.splice(bs.data, off as nat, enc()))
    {
      IntEncoding.UInt64Put(sz, off, bs);
      attrs.put(off + 8, bs);
    }
  }

  datatype preInode = Mk(meta: Meta, blks: seq<uint64>)
  {
    const sz: uint64 := meta.sz
    const ty: InodeType := meta.ty

    static const preZero: preInode := Mk(Meta(0, Attrs.zero), C.repeat(0 as uint64, 12))

    ghost predicate Valid()
    {
      && |blks| == 12
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
    IntEncoding.lemma_enc_32_0();
    zero_encode_seq_uint64(12);
    reveal enc();
  }

  ghost function {:opaque} enc(i: Inode): (bs:seq<byte>)
    ensures |bs| == 128
  {
    assert i.Valid();
    var blk_enc := seq_enc_uint64(i.blks);
    enc_uint64_len(i.blks);
    i.meta.enc() + blk_enc
  }

  lemma enc_app(i: Inode)
    ensures enc(i) ==
    IntEncoding.le_enc64(i.meta.sz) + i.meta.attrs.enc() +
    seq_enc_uint64(i.blks)
  {
    reveal enc();
  }

  method decode_meta(bs: Bytes, off: uint64, ghost m: Meta)
    returns (m': Meta)
    requires bs.Valid()
    requires off as nat + 32 <= |bs.data|
    requires bs.data[off .. off as nat + 32] == m.enc()
    ensures m' == m
  {
    assert bs.data[off..off + 8] == m.enc()[..8] by {
      C.double_subslice_auto(bs.data);
    }
    var sz := Marshal.UInt64Decode(bs, off, m.sz);
    var attrs := Attrs.decode(bs, off + 8, m.attrs);
    return Meta(sz, attrs);
  }
}
