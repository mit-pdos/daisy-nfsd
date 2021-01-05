type byte = bv8
type uint64 = x:int | 0 <= x < 0x1_0000_0000_0000_0000
// TODO: switch to this
newtype {:nativeType "ulong"} native_u64 = x:int | 0 <= x < 0x1_0000_0000_0000_0000

module {:extern "bytes", "github.com/tchajed/bytes"} bytes {
    type byte = bv8

    class {:extern} Bytes {
        function {:extern} data(): seq<byte>
        reads this

        constructor {:extern} ()
        ensures data() == []

        method {:extern} Get(i: nat)
        returns (x: byte)
        modifies {}
        requires i < |data()|
        ensures x == data()[i]

        method {:extern} Append(b: byte)
        modifies this
        ensures data() == old(data()) + [b]
    }
}

module bytes_test {
    import opened bytes

    method UseBytes() {
        var bs := new Bytes();
        bs.Append(0);
        bs.Append(1);
        var b0 := bs.Get(0);
        var b1 := bs.Get(1);
        assert b0 == 0;
        assert b1 == 1;
    }
}
