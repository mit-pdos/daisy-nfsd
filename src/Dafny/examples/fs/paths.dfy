include "dirent.dfy"

module Paths {
  import opened Std
  import opened Machine
  import opened ByteSlice

  import opened DirEntries

  method Pathc?(name: Bytes) returns (p:bool)
    requires name.Valid()
    ensures p == is_pathc(name.data)
  {
    var i: uint64 := 0;
    var len := name.Len();
    if len > path_len_u64 {
      return false;
    }
    while i < len
      invariant 0 <= i as nat <= |name.data|
      invariant is_pathc(name.data[..i])
    {
      if name.Get(i) == 0 {
        return false;
      }
      i := i + 1;
    }
    return true;
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

  method NullTerminatePrefix(bs: Bytes)
    requires bs.Valid()
    modifies bs
    ensures bs.data == decode_null_terminated(old(bs.data))
  {
    var i: uint64 := 0;
    var len: uint64 := bs.Len();
    while i < len
      modifies bs
      invariant i as nat <= |bs.data|
      invariant forall k: nat | k < i as nat :: bs.data[k] != 0
      invariant decode_null_terminated(bs.data) == bs.data[..i] + decode_null_terminated(bs.data[i..])
      invariant bs.data == old(bs.data)
    {
      var b := bs.Get(i);
      if b == 0 {
        bs.Subslice(0, i);
        return;
      }
      i := i + 1;
    }
    return;
  }

  method PadPathc(bs: Bytes)
    modifies bs
    requires is_pathc(bs.data)
    ensures bs.data == encode_pathc(old(bs.data))
  {
    var zeros := NewBytes(path_len_u64 - bs.Len());
    bs.AppendBytes(zeros);
  }

}
