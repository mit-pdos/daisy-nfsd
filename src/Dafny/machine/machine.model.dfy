include "machine_s.dfy"

module bytes_model refines bytes {
    class {:compile false} Bytes {
        var data_: seq<byte>;

        function data(): seq<byte>
        {
            data_
        }

        constructor(sz: uint64)
        {
            this.data_ := repeat(0 as byte, sz as nat);
        }

        method Get(i: uint64)
        returns (x:byte)
        {
            return data_[i];
        }

        method Append(b: byte)
        {
            data_ := data_ + [b];
        }
    }
}
