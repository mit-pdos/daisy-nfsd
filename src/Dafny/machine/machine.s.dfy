include "../util/collections.dfy"

module Machine {
    type byte = bv8
    newtype {:nativeType "ulong"} uint64 = x:int | 0 <= x < 0x1_0000_0000_0000_0000

    predicate no_overflow(x: nat, y: int)
    {
        0 <= x + y < U64.MAX
    }

    function method sum_overflows(x: uint64, y: uint64): (overflow:bool)
        ensures !overflow == no_overflow(x as nat, y as nat)
    {
        // discovered by trial and error
        x > (0xFFFF_FFFF_FFFF_FFFF-y)
    }

    // NOTE(tej): I wanted this to be in module U64, but Dafny imports children
    // modules into their parents but not the other way around, so there's no
    // way to do that without making U64 a separate module (which I don't know
    // how to re-export)
    predicate no_overflow_u64(x: uint64, y: int)
    {
        no_overflow(x as nat, y)
    }

    function method min_u64(x: uint64, y: uint64): uint64
    {
        if x < y then x else y
    }

    lemma min_u64_lb(x: uint64, y: uint64)
        ensures min_u64(x, y) <= x && min_u64(x, y) <= y
    {}

    function method max_u64(x: uint64, y: uint64): uint64
    {
        if x > y then x else y
    }

    lemma max_u64_ub(x: uint64, y: uint64)
        ensures x <= max_u64(x, y) && y <= max_u64(x, y)
    {}

    module U64 {
        const MAX: nat := 0x1_0000_0000_0000_0000
    }
}

module {:extern "bytes", "github.com/mit-pdos/dafny-jrnl/src/dafny_go/bytes"} ByteSlice {
    import opened Machine
    import C = Collections

    // the implementations in this module serve as a feasibility check for the API
    class {:extern} Bytes {
        var data: seq<byte>

        predicate Valid()
        reads this
        {
            |data| < U64.MAX
        }

        constructor {:extern} (data_: seq<byte>)
        requires |data_| < U64.MAX
        ensures Valid()
        ensures data == data_
        {
            this.data := data_;
        }

        function method {:extern} Len(): (len:uint64)
        reads this
        requires Valid()
        ensures len as nat == |data|
        {
            |data| as uint64
        }

        function method {:extern} Get(i: uint64): (x: byte)
        reads this
        requires i as nat < |data|
        ensures x == data[i]
        {
            data[i]
        }

        method {:extern} Set(i: uint64, b: byte)
        modifies this
        ensures old(Valid()) ==> Valid()
        requires i as nat < |data|
        ensures data == old(data)[i as nat:=b]
        {
            data := data[i as nat := b];
        }

        method {:extern} Append(b: byte)
        modifies this
        requires Valid() ensures Valid()
        requires no_overflow(|data|, 1)
        ensures data == old(data) + [b]
        {
            data := data + [b];
        }

        method {:extern} AppendBytes(bs: Bytes)
            modifies this
            // NOTE: I did not think of this initially, until the model proof
            // caught it
            requires bs != this
            ensures old(Valid()) ==> Valid()
            requires bs.Valid()
            requires no_overflow(|data|, |bs.data|)
            ensures data == old(data) + bs.data
        {
            data := data + bs.data;
        }

        method {:extern} Subslice(start: uint64, end: uint64)
            modifies this
            ensures old(Valid()) ==> Valid()
            requires start as nat <= end as nat <= |data|
            ensures data == old(data[start..end])
            ensures |data| == (end-start) as nat
        {
            data := data[start..end];
        }

        method {:extern} CopyTo(off: uint64, bs: Bytes)
            modifies this
            ensures old(Valid()) ==> Valid()
            requires bs != this
            requires off as nat + |bs.data| <= |this.data|
            ensures data == old(C.splice(data, off as nat, bs.data))
            ensures |data| == old(|data|)
            ensures bs.data == old(bs.data)
        {
            data := C.splice(data, off as nat, bs.data);
        }

        method {:extern} Split(off: uint64) returns (bs: Bytes)
            modifies this
            ensures fresh(bs)
            requires off as nat <= |data|
            requires Valid() ensures Valid()
            ensures bs.Valid()
            ensures data == old(data[..off as nat])
            ensures bs.data == old(data[off as nat..])
        {
            var rest := data[off as nat..];
            data := data[..off as nat];
            bs := new Bytes(rest);
        }
    }

    method {:extern} NewBytes(sz: uint64)
    returns (bs:Bytes)
    ensures fresh(bs)
    ensures bs.Valid()
    ensures bs.data == C.repeat(0 as byte, sz as nat)
    {
        return new Bytes(C.repeat(0 as byte, sz as nat));
    }
}

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
}
