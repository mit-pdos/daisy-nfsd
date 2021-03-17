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
    ghost var blks: seq<uint64>

    const bs: Bytes

    ghost const Repr: set<object> := {this, bs}

    // the inode represented
    function val(): Inode.Inode
      reads Repr
      requires Valid()
    {
      reveal Valid();
      Inode.Mk(Inode.Meta(sz, ty), blks)
    }

    predicate has(i: Inode.Inode)
      reads Repr
    {
      && Valid()
      && val() == i
    }

    predicate {:opaque} Valid()
      reads Repr
    {
      && |blks| == 14
      && sz as nat <= Inode.MAX_SZ
      && |bs.data| == 128
      && Marshal.decode_uint64_seq(bs.data[16..]) == blks
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
      var sz := IntEncoding.UInt64Get(bs, 0);
      assert sz == i.meta.sz by {
        assert bs.data[..8] == IntEncoding.le_enc64(i.meta.sz);
        IntEncoding.lemma_le_enc_dec64(i.meta.sz);
      }
      var ty_u64 := IntEncoding.UInt64Get(bs, 8);
      var ty := Inode.InodeType.from_u64(ty_u64);
      assert ty == i.meta.ty by {
        i.meta.ty.enc_dec();
      }

      this.sz := sz;
      this.ty := ty;

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
      IntEncoding.UInt64Put(ty.to_u64(), 8, this.bs);
      bs := this.bs;
      assert bs.data[16..] == old(bs.data[16..]);
      Inode.enc_app(val());
    }

    method get_blk(k: uint64) returns (bn: uint64)
      requires Valid()
      requires k < 14
      ensures |blks| == 14
      ensures bn == blks[k]
    {
      reveal Valid();
      bn := IntEncoding.UInt64Get(this.bs, 16 + 8 * k);
      assert bs.data[16 + 8*k .. 16 + 8*k + 8] ==
        bs.data[16..][8*k .. 8*k + 8];
      Marshal.decode_uint64_seq_one_spec(bs.data[16..], k as nat);
    }

    method set_blk(k: uint64, bn: uint64)
      modifies Repr
      requires Valid() ensures Valid()
      requires k < 14
      ensures |old(blks)| == 14
      ensures blks == old(blks[k as nat := bn])
      ensures sz == old(sz)
      ensures ty == old(ty)
    {
      reveal Valid();
      Marshal.decode_uint64_seq_modify_one(bs.data[16..], k as nat, bn);
      IntEncoding.UInt64Put(bn, 16 + k*8, this.bs);
      assert bs.data[16..] ==
        old(C.splice(bs.data[16..], k as nat*8, IntEncoding.le_enc64(bn)));
      blks := blks[k as nat := bn];
    }

    method set_ty(ty: Inode.InodeType)
      modifies this
      requires Valid() ensures Valid()
      ensures blks == old(blks)
      ensures sz == old(sz)
      ensures this.ty == ty
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
    {
      this.sz := sz;
      reveal Valid();
    }
  }

}
