include "machine.s.dfy"

// This model ensures that the bytes extern interface is feasible (that it has
// no contradictions). See
// https://github.com/dafny-lang/dafny/wiki/Modeling-External-State-Correctly
// for a complete description of this approach.

module bytes_model refines bytes {
    class {:compile false} Bytes {
        var data_: seq<byte>;

        predicate Valid()
        {
            |data_| < 0x1_0000_0000_0000_0000
        }

        function method data(): seq<byte>
        {
            data_
        }

        constructor(data_: seq<byte>)
        {
            this.data_ := data_;
        }

        function method Get(i: uint64): (x:byte)
        {
            data_[i]
        }

        method Append(b: byte)
        {
            data_ := data_ + [b];
        }
    }

    method {:compile false} NewBytes(sz: uint64)
    returns (bs:Bytes)
    {
       return new Bytes(repeat(0 as byte, sz as nat));
    }
}
