include "../machine/bytes.s.dfy"

module ByteHelpers {
  import opened ByteSlice
  import opened Machine

  method isZero(bs: Bytes)
    returns (yes: bool)
    requires bs.Valid()
    ensures yes == (forall i:nat | i < |bs.data| :: bs.data[i] == 0)
  {
    var i: uint64 := 0;
    var len := bs.Len();
    while i < len
      invariant i as nat <= |bs.data|
      invariant forall j:nat | j < i as nat :: bs.data[j] == 0
    {
      var b := bs.Get(i);
      if b != 0 {
        return false;
      }
      i := i + 1;
    }
    return true;
  }

  method Equal(bs1: Bytes, bs2: Bytes)
    returns (eq: bool)
    requires bs1.Valid() && bs2.Valid()
    ensures eq == (bs1.data == bs2.data)
  {
    if bs1.Len() != bs2.Len() {
      return false;
    }
    var i: uint64 := 0;
    var len := bs1.Len();
    while i < len
      invariant i as nat <= |bs1.data|
      invariant forall j:nat | j < i as nat :: bs1.data[j] == bs2.data[j]
    {
      var b1 := bs1.Get(i);
      var b2 := bs2.Get(i);
      if b1 != b2 {
        return false;
      }
      i := i + 1;
    }
    return true;
  }

  method CopyTo(bs0: Bytes, off: uint64, bs: Bytes)
      modifies bs0
      requires bs != bs0
      requires bs.Valid()
      requires off as nat + |bs.data| <= |bs0.data|
      ensures bs0.data == old(C.splice(bs0.data, off as nat, bs.data))
      ensures |bs0.data| == old(|bs0.data|)
      ensures bs.data == old(bs.data)
  {
    var len := bs.Len();
    bs0.CopySegment(off, bs, 0, len);
  }

  method CopyFrom(bs0: Bytes, bs: Bytes, off: uint64, len: uint64)
      modifies bs0
      requires bs != bs0
      requires off as nat + len as nat <= |bs.data|
      requires len as nat <= |bs0.data|
      ensures bs0.data == bs.data[off as nat..off as nat + len as nat] + old(bs0.data[len as nat..])
  {
    bs0.CopySegment(0, bs, off, len);
  }

}
