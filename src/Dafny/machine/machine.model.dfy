include "machine.s.dfy"

// This model ensures that the ByteSlice extern interface is feasible (that it has
// no contradictions). See
// https://github.com/dafny-lang/dafny/wiki/Modeling-External-State-Correctly
// for a complete description of this approach.

module ByteSlice_model refines ByteSlice {
    class {:compile false} Bytes {
        constructor(data_: seq<byte>)
        {
            this.data := data_;
        }

        function method Get(i: uint64): (x:byte)
        {
            data[i]
        }

        method Append(b: byte)
        {
            data := data + [b];
        }
    }

    method {:compile false} NewBytes(sz: uint64)
    returns (bs:Bytes)
    {
       return new Bytes(repeat(0 as byte, sz as nat));
    }
}
