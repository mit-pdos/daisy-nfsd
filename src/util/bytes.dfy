include "../machine/bytes.s.dfy"
include "../machine/machine.s.dfy"

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
}
