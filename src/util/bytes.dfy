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
}
