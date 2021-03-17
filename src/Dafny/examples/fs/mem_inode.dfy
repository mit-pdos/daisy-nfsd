include "inode.dfy"

module MemInodes {
  import opened Machine
  import opened ByteSlice

  import Inode
  import Marshal
  import IntEncoding

  class MemInode
  {
    var sz: uint64
    var ty: Inode.InodeType
    var attrs: Inode.Attrs
    ghost var blks: seq<uint64>

    const bs: Bytes

    ghost const Repr: set<object> := {this, bs}

    // the inode represented
    function val(): Inode.Inode
      reads Repr
      requires Valid()
    {
      reveal Valid();
      Inode.Mk(Inode.Meta(sz, ty, attrs), blks)
    }

    predicate {:opaque} Valid()
      reads Repr
    {
      && |blks| == 12
      && sz as nat <= Inode.MAX_SZ
      && |bs.data| == 128
      && Marshal.decode_uint64_seq(bs.data[32..]) == blks
    }

    function method meta(): Inode.Meta
      reads this
    {
      Inode.Meta(sz, ty, attrs)
    }

    constructor(bs: Bytes, ghost i: Inode.Inode)
      modifies bs
      requires bs.data == Inode.enc(i)
      ensures Valid()
      ensures this.bs == bs
      ensures val() == i
    {
      assert |bs.data| == 128;
      this.bs := bs;
      this.blks := i.blks;

      Inode.enc_app(i);
      var m := Inode.decode_meta(bs, 0, i.meta);

      this.sz := m.sz;
      this.ty := m.ty;
      this.attrs := m.attrs;

      new;
      reveal Valid();
      Marshal.decode_encode_uint64_seq_id(i.blks);
    }

    method encode() returns (bs: Bytes)
      modifies this.bs
      requires Valid()
      ensures bs.data == Inode.enc(old(val()))
      ensures bs == this.bs
    {
      reveal Valid();
      IntEncoding.UInt64Put(sz, 0, this.bs);
      IntEncoding.UInt32Put(ty.to_u32(), 8, this.bs);
      attrs.put(12, this.bs);
      bs := this.bs;
      assert bs.data[32..] == old(bs.data[32..]);
      Inode.enc_app(val());
    }

    method get_blk(k: uint64) returns (bn: uint64)
      requires Valid()
      requires k < 12
      ensures |blks| == 12
      ensures bn == blks[k]
    {
      reveal Valid();
      bn := IntEncoding.UInt64Get(this.bs, 32 + 8 * k);
      assert bs.data[32 + 8*k .. 32 + 8*k + 8] ==
        bs.data[32..][8*k .. 8*k + 8];
      Marshal.decode_uint64_seq_one_spec(bs.data[32..], k as nat);
    }

    method set_blk(k: uint64, bn: uint64)
      modifies Repr
      requires Valid() ensures Valid()
      requires k < 12
      ensures |old(blks)| == 12
      ensures blks == old(blks[k as nat := bn])
      ensures sz == old(sz)
      ensures ty == old(ty)
      ensures attrs == old(attrs)
    {
      reveal Valid();
      Marshal.decode_uint64_seq_modify_one(bs.data[32..], k as nat, bn);
      IntEncoding.UInt64Put(bn, 32 + k*8, this.bs);
      assert bs.data[32..] ==
        old(C.splice(bs.data[32..], k as nat*8, IntEncoding.le_enc64(bn)));
      blks := blks[k as nat := bn];
    }

    method set_ty(ty: Inode.InodeType)
      modifies this
      requires Valid() ensures Valid()
      ensures blks == old(blks)
      ensures sz == old(sz)
      ensures this.ty == ty
      ensures attrs == old(attrs)
    {
      this.ty := ty;
      reveal Valid();
    }

    method set_sz(sz: uint64)
      modifies this
      requires sz as nat <= Inode.MAX_SZ
      requires Valid() ensures Valid()
      ensures blks == old(blks)
      ensures this.sz == sz
      ensures ty == old(ty)
      ensures attrs == old(attrs)
    {
      this.sz := sz;
      reveal Valid();
    }

    method set_attrs(attrs: Inode.Attrs)
      modifies this
      requires Valid() ensures Valid()
      ensures blks == old(blks)
      ensures sz == old(sz)
      ensures ty == old(ty)
      ensures this.attrs == attrs
    {
      this.attrs := attrs;
      reveal Valid();
    }
  }

}
