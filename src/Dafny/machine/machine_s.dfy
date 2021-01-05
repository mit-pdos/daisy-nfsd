include "../util/collections.dfy"

module Machine {
    type byte = bv8
    type {:nativeType "ulong"} uint64 = x:int | 0 <= x < 0x1_0000_0000_0000_0000
}


module {:extern "bytes", "github.com/mit-pdos/dafny-jrnl/src/dafny_go/bytes"} bytes {
    import opened Machine
    import opened Collections

    class {:extern} Bytes {
        function {:extern} data(): seq<byte>
        reads this

        constructor {:extern} (data_: seq<byte>)
        ensures data() == data_

        method {:extern} Get(i: uint64)
        returns (x: byte)
        modifies {}
        requires i < |data()|
        ensures x == data()[i]

        method {:extern} Append(b: byte)
        modifies this
        ensures data() == old(data()) + [b]
    }

    method {:extern} NewBytes(sz: uint64)
    returns (bs:Bytes)
    ensures fresh(bs)
    ensures bs.data() == repeat(0 as byte, sz as nat)
}

module bytes_test {
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
}
