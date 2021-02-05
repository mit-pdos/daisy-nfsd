include "jrnl.s.dfy"

module Alloc
{
  import opened Machine
  import J = JrnlSpec

  class MaxAllocator
  {
    const alloc: J.Allocator;
    const max: uint64;

    predicate {:opaque} Valid()
    {
      && 8 <= max
      && max%8 == 0
    }

    function Repr(): set<object>
    {
      {alloc}
    }

    constructor(max: uint64)
      requires 0 < max
      requires max % 8 == 0
      ensures Valid()
      ensures fresh(Repr())
      ensures this.max == max
    {
      var alloc := J.NewAllocator(max);
      alloc.MarkUsed(0);
      this.alloc := alloc;
      this.max := max;
      new;
      reveal_Valid();
    }

    method Alloc() returns (x:uint64)
      modifies Repr()
      requires Valid() ensures Valid()
      ensures 0 < x < max
    {
      x := alloc.Alloc();
      if !(0 < x < max) {
        x := 1;
      }
      reveal_Valid();
    }

    method MarkUsed(x: uint64)
      modifies Repr()
      requires Valid() ensures Valid()
    {
      this.alloc.MarkUsed(x);
    }

    method Free(x: uint64)
      modifies Repr()
      requires Valid() ensures Valid()
    {
      if 0 < x < max {
        this.alloc.Free(x);
      }
    }
  }
}
