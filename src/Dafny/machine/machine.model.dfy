include "machine_s.dfy"

module bytes_model refines bytes {
    class {:compile false} Bytes {
        var data_: seq<byte>;

        function data(): seq<byte>
        {
            data_
        }

        constructor()
        {
            this.data_ := [];
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
