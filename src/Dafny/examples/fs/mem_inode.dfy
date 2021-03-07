include "inode.dfy"

module MemInode {
  import opened Machine
  import opened ByteSlice

  import Inode
  import Marshal
  import IntEncoding

  class MemInode
  {
    // the inode represented
    var sz: uint64
    var ty: Inode.InodeType
    ghost var blks: seq<uint64>

    const bs: Bytes

    ghost const Repr: set<object> := {this, bs}

    function val(): Inode.Inode
      reads Repr
      requires Valid()
    {
      reveal Valid();
      Inode.Mk(Inode.Meta(sz, ty), blks)
    }

    predicate {:opaque} Valid()
      reads this, bs
    {
      && |blks| == 14
      && sz as nat <= Inode.MAX_SZ
      && |bs.data| == 128
      && bs.data[16..] == Marshal.seq_enc_uint64(blks)
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

      assert Marshal.seq_encode(Inode.inode_enc(i)) == bs.data by {
        reveal Inode.enc();
      }
      var dec := new Marshal.Decoder.Init(bs, Inode.inode_enc(i));
      var sz := dec.GetInt(i.meta.sz);
      this.sz := sz;
      var ty_u64 := dec.GetInt(i.meta.ty.to_u64());
      i.meta.ty.from_to_u64();
      var ty := Inode.InodeType.from_u64(ty_u64);
      this.ty := ty;
      Inode.enc_app(i);
      new;
      reveal Valid();
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
      assert bs.data[16 + 8 * k .. 16 + 8 * k + 8] == bs.data[16..][8*k .. 8*k + 8];
      Marshal.enc_uint64_get_one(blks, k as nat);
      IntEncoding.lemma_le_enc_dec64(blks[k]);
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
      IntEncoding.UInt64Put(bn, 16 + 8 * k, this.bs);
      blks := blks[k as nat := bn];
      // TODO: do this proof with seq_encode_concat and concat homogeneous splice lemma
      assume false;
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
