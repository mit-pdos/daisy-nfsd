include "bytes.s.dfy"

module bytes_test {
  import opened Machine
  import opened ByteSlice

  method UseBytes() {
    var bs := NewBytes(1);
    bs.Append(0);
    bs.Append(1);
    var b0 := bs.Get(1);
    var b1 := bs.Get(2);
    assert b0 == 0;
    assert b1 == 1;
  }

  method UseUint64(x: uint64)
    returns (y:uint64)
    requires x as nat + 1 < U64.MAX
  {
    return x + 1;
  }

  method TestSublice()
  {
    // mirror of Go test to check Subslice against concrete values
    //
    // the spec is written in terms of Dafny sequence operations and there's
    // always a question of off-by-one errors in their interpretation
    // (though luckily it happens to be that Go and Dafny agree)

    // the Go test we're copying
    /*
    bs := NewBytes(5)
    bs.Set(1, 3)
    bs.Set(2, 4)
    bs.Subslice(1, 3)
    assert.Equal(t, uint64(2), bs.Len())
    assert.Equal(t, byte(3), bs.Get(0))
    assert.Equal(t, byte(4), bs.Get(1))
    */

    var bs := NewBytes(5);
    bs.Set(1, 3);
    bs.Set(2, 4);
    bs.Subslice(1, 3);
    assert 2 as uint64 == bs.Len();
    assert 3 as byte == bs.Get(0);
    assert 4 as byte == bs.Get(1);
  }

  method TestCopySegment()
  {
    // mirror of this Go test:
    /*
       bs := NewBytes(5)
       bs.Set(2, 3)
       bs2 := NewBytes(2)
       bs2.CopyFrom(bs, 2, 1)
       assert.Equal(t, byte(3), bs2.Get(0))
    */
    var bs := NewBytes(5);
    bs.Set(2, 3);
    var bs2 := NewBytes(3);
    bs2.Set(0, 1);
    bs2.Set(2, 2);

    bs2.CopySegment(1, bs, 2, 1);

    assert bs.data == [0,0,3,0,0];
    assert bs2.data == [1,3,2];
  }

  method TestCopySegmentClone(bs: Bytes) returns (bs':Bytes)
    requires bs.Valid()
    ensures fresh(bs')
    ensures bs'.data == bs.data
  {
    var len := bs.Len();
    bs' := NewBytes(len);
    bs'.CopySegment(0, bs, 0, len);
  }
}
