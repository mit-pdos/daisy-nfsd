include "machine.dfy"

module {:extern "bytes", "github.com/mit-pdos/daisy-nfsd/dafny_go/bytes"} ByteSlice {
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
        requires i as nat < |data|
        ensures data == old(data)[i as nat:=b]
        {
            data := data[i as nat := b];
        }

        method {:extern} Append(b: byte)
        modifies this
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
            requires no_overflow(|data|, |bs.data|)
            ensures data == old(data) + bs.data
        {
            data := data + bs.data;
        }

        method {:extern} Subslice(start: uint64, end: uint64)
            modifies this
            requires start as nat <= end as nat <= |data|
            ensures data == old(data[start..end])
            ensures |data| == (end-start) as nat
        {
            data := data[start..end];
        }

        method {:extern} CopyTo(off: uint64, bs: Bytes)
            modifies this
            requires bs != this
            requires off as nat + |bs.data| <= |this.data|
            ensures data == old(C.splice(data, off as nat, bs.data))
            ensures |data| == old(|data|)
            ensures bs.data == old(bs.data)
        {
            data := C.splice(data, off as nat, bs.data);
        }

        method {:extern} CopyFrom(bs: Bytes, off: uint64, len: uint64)
            modifies this
            requires bs != this
            requires off as nat + len as nat <= |bs.data|
            requires len as nat <= |data|
            ensures data == bs.data[off as nat..off as nat + len as nat] + old(data[len as nat..])
        {
            data := C.splice(data, 0, bs.data[off as nat..off as nat + len as nat]);
        }

        method {:extern} Split(off: uint64) returns (bs: Bytes)
            modifies this
            ensures fresh(bs)
            requires off as nat <= |data|
            requires Valid()
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
    ensures bs.data == C.repeat(0 as byte, sz as nat)
    {
        return new Bytes(C.repeat(0 as byte, sz as nat));
    }
}
