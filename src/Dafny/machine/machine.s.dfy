include "../util/collections.dfy"

module Machine {
    type byte = bv8
    newtype {:nativeType "ulong"} uint64 = x:int | 0 <= x < 0x1_0000_0000_0000_0000
}

module {:extern "bytes", "github.com/mit-pdos/dafny-jrnl/src/dafny_go/bytes"} bytes {
    import opened Machine
    import opened Collections

    class {:extern} Bytes {
        var data: seq<byte>

        predicate Valid()
        reads this
        {
            |data| < 0x1_0000_0000_0000_0000
        }

        // NOTE(tej): both the constructor and data are available in code in
        // order to write the feasibility of Jrnl; it would be nice to separate
        // these out, so that the model of Jrnl depends on the model of bytes.

        constructor {:extern} (data_: seq<byte>)
        requires |data_| < 0x1_0000_0000_0000_0000
        ensures Valid()
        ensures data == data_

        function method {:extern} Len(): (len:uint64)
        reads this
        requires Valid()
        ensures len as nat == |data|

        function method {:extern} Get(i: uint64): (x: byte)
        reads this
        requires Valid()
        requires i as nat < |data|
        ensures x == data[i]

        method {:extern} Set(i: uint64, b: byte)
        modifies this
        requires Valid() ensures Valid()
        requires i as nat < |data|
        ensures data == old(data)[i as nat:=b]

        method {:extern} Append(b: byte)
        modifies this
        requires Valid() ensures Valid()
        requires |data| < 0x1_0000_0000_0000_0000-1
        ensures data == old(data) + [b]
    }

    method {:extern} NewBytes(sz: uint64)
    returns (bs:Bytes)
    ensures fresh(bs)
    ensures bs.Valid()
    ensures bs.data == repeat(0 as byte, sz as nat)
}

module bytes_test {
    import opened Machine
    import opened bytes

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
    requires x as nat < 0x1_0000_0000_0000_0000-1
    {
        return x + 1;
    }
}
