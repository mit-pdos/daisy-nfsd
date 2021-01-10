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

    module U64 {
        const MAX: nat := 0x1_0000_0000_0000_0000
    }
}

module {:extern "bytes", "github.com/mit-pdos/dafny-jrnl/src/dafny_go/bytes"} ByteSlice {
    import opened Machine
    import opened Collections

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
        requires Valid()
        requires i as nat < |data|
        ensures x == data[i]
        {
            data[i]
        }

        method {:extern} Set(i: uint64, b: byte)
        modifies this
        requires Valid() ensures Valid()
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
    }

    method {:extern} NewBytes(sz: uint64)
    returns (bs:Bytes)
    ensures fresh(bs)
    ensures bs.Valid()
    ensures bs.data == repeat(0 as byte, sz as nat)
    {
        return new Bytes(repeat(0 as byte, sz as nat));
    }
}

module ImmutableByteSlice {
    import opened Machine
    import opened ByteSlice

    // FIXME: this isn't actually that useful because the caller can't abstract
    // over whether or not a byte slice is immutable, and we have to make sure
    // not to access bs directly or we can mutate the byte slice anyway.
    class ImmutableBytes
    {
        var bs: Bytes;
        ghost const data: seq<byte>;

        predicate Valid()
        reads this, this.bs
        {
            && bs.Valid()
            && data == bs.data
        }

        constructor(bs: Bytes)
        requires bs.Valid()
        ensures Valid()
        ensures this.data == bs.data
        {
            this.bs := bs;
            this.data := bs.data;
        }

        method Len()
        returns (sz:uint64)
        requires Valid()
        modifies {}
        ensures sz as nat == |data|
        {
            return bs.Len();
        }

        method Get(i: uint64)
        returns (x:byte)
        modifies {}
        requires Valid()
        requires i as nat < |data|
        ensures x == data[i as nat]
        {
            return bs.Get(i);
        }
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
}
