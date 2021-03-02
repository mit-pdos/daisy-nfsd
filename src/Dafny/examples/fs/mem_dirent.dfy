include "dirent.dfy"

module MemDirEntries
{
  import opened Std
  import opened DirEntries
  import opened Machine
  import opened ByteSlice
  import opened FsKinds
  import IntEncoding

  datatype MemDirEnt = MemDirEnt(name: Bytes, ino: Ino)
  {
    function val(): DirEnt
      reads name
      requires Valid()
    {
      DirEnt(name.data, ino)
    }

    predicate Valid()
      reads name
    {
      && is_pathc(name.data)
    }
  }

  method NullTerminatedEqualSmaller(bs1: Bytes, bs2: Bytes) returns (p:bool)
    requires bs1.Valid() && bs2.Valid()
    requires bs1.Len() <= bs2.Len()
    ensures p == (decode_null_terminated(bs1.data) == decode_null_terminated(bs2.data))
  {
    var i: uint64 := 0;
    var len: uint64 := bs1.Len();
    while i < len
      invariant 0 <= i as nat <= |bs1.data|
      invariant bs1.data[..i] == bs2.data[..i]
      invariant decode_null_terminated(bs1.data) == bs1.data[..i] + decode_null_terminated(bs1.data[i..])
      invariant decode_null_terminated(bs2.data) == bs2.data[..i] + decode_null_terminated(bs2.data[i..])

    {
      var b1 := bs1.Get(i);
      var b2 := bs2.Get(i);
      if b1 == 0 || b2 == 0 {
        return b1 == b2;
      }
      assert b1 != 0 && b2 != 0;
      if b1 != b2 {
        assert decode_null_terminated(bs1.data)[i] == b1;
        assert decode_null_terminated(bs2.data)[i] == b2;
        return false;
      }
      i := i + 1;
    }
    if bs1.Len() == bs2.Len() {
      return true;
    }
    assert bs1.Len() < bs2.Len();
    var last := bs2.Get(bs1.Len());
    return last == 0;
  }

  method NullTerminatedEqual(bs1: Bytes, bs2: Bytes) returns (p:bool)
    requires bs1.Valid() && bs2.Valid()
    ensures p == (decode_null_terminated(bs1.data) == decode_null_terminated(bs2.data))
  {
    if bs1.Len() <= bs2.Len() {
      p := NullTerminatedEqualSmaller(bs1, bs2);
      return;
    }
    p := NullTerminatedEqualSmaller(bs2, bs1);
    return;
  }

  class MemDirents
  {
    ghost var val: Dirents
    const bs: Bytes

    ghost const Repr: set<object> := {this, bs}

    predicate Valid()
      reads Repr
    {
      && bs.data == val.enc()
      && |bs.data| == 4096
    }

    constructor(bs: Bytes, ghost dents: Dirents)
      requires bs.data == dents.enc()
      ensures Valid()
      ensures val == dents
    {
      this.bs := bs;
      this.val := dents;
      new;
      val.enc_len();
    }

    lemma data_one(k: nat)
      requires Valid()
      requires k < 128
      ensures bs.data[k*32..(k+1) * 32] == val.s[k].enc()
    {
      C.concat_homogeneous_one_list(C.seq_fmap(Dirents.encOne, val.s), k, 32);
    }

    lemma data_one_ino(k: nat)
      requires Valid()
      requires k < 128
      ensures bs.data[k*32 + 24..k*32 + 32] == IntEncoding.le_enc64(val.s[k].ino)
    {
      data_one(k);
      val.s[k].enc_app();
      assert bs.data[k*32..(k+1)*32][24..32] == bs.data[k*32 + 24..k*32 + 32];
    }

    method get_ino(k: uint64) returns (ino: Ino)
      requires Valid()
      requires k < 128
      ensures ino == val.s[k].ino
    {
      // we'll prove it's an Ino later, for now it's just a uint64
      var ino': uint64 := IntEncoding.UInt64Get(bs, k*32 + 24);
      data_one_ino(k as nat);
      IntEncoding.lemma_le_enc_dec64(val.s[k].ino);
      ino := ino';
    }

    method get_name(k: uint64) returns (name: Bytes)
      requires Valid()
      requires k < 128
      ensures fresh(name) && name.Valid() && |name.data| == 24
      ensures encode_pathc(val.s[k].name) == name.data
    {
      name := NewBytes(24);
      name.CopyFrom(bs, k*32, 24);
      data_one(k as nat);
      val.s[k].enc_app();
      assert bs.data[k*32..(k+1)*32][..24] == bs.data[k*32..k*32 + 24];
    }

    method is_used(k: uint64) returns (p:bool)
      requires Valid()
      requires k < 128
      ensures p == val.s[k].used()
    {
      var ino := get_ino(k);
      p := ino != 0;
    }

    method is_name(k: uint64, needle: Bytes) returns (r:Option<Ino>)
      requires Valid()
      requires k < 128
      requires needle.Valid()
      requires is_pathc(needle.data)
      ensures r.None? ==> !(val.s[k].used() && val.s[k].name == needle.data)
      ensures r.Some? ==> val.s[k].used() && val.s[k].name == needle.data && val.s[k].ino == r.x
    {
      var ino := get_ino(k);
      if ino == 0 {
        return None;
      }
      var name := get_name(k);
      assert decode_null_terminated(name.data) == val.s[k].name by {
        decode_encode(val.s[k].name);
      }
      decode_nullterm_no_null(needle.data);
      var equal := NullTerminatedEqualSmaller(needle, name);
      if equal {
        return Some(ino);
      } else {
        return None;
      }
    }

    method findFree() returns (free_i: uint64)
      requires Valid()
      ensures free_i as nat == val.findFree()
    {
      var i: uint64 := 0;
      while i < 128
        invariant 0 <= i as nat <= 128
        invariant forall k:nat | k < i as nat :: val.s[k].used()
      {
        var p := is_used(i);
        if !p {
          C.find_first_characterization(Dirents.is_unused, val.s, i as nat);
          return i;
        }
        i := i + 1;
      }
      C.find_first_characterization(Dirents.is_unused, val.s, 128);
      return 128;
    }

    method findName(name: Bytes) returns (r: Option<(uint64, Ino)>)
      requires Valid()
      requires name.Valid() && is_pathc(name.data)
      ensures r.None? ==> name.data !in val.dir
      ensures r.Some? ==>
      && name.data in val.dir
      && r.x.0 < 128
      && r.x.0 as nat == val.findName(name.data)
      && val.dir[name.data] == r.x.1
    {
      ghost var p: PathComp := name.data;
      var i: uint64 := 0;
      while i < 128
        invariant 0 <= i as nat <= 128
        invariant forall k:nat | k < i as nat :: !(val.s[k].used() && val.s[k].name == p)
      {
        var ino := is_name(i, name);
        if ino.Some? {
          C.find_first_characterization(preDirents.findName_pred(p), val.s, i as nat);
          assert val.findName(p) == i as nat;
          val.findName_found(p);
          return Some( (i, ino.x) );
        }
        i := i + 1;
      }
      C.find_first_characterization(preDirents.findName_pred(p), val.s, 128);
      val.findName_not_found(p);
      return None;
    }
  }
}
