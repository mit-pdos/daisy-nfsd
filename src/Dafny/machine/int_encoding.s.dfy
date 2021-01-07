/*
Experiment with little-endian encoding of integers.

IronFleet has good code for this at
https://github.com/GLaDOS-Michigan/IronFleet/blob/master/ironfleet/src/Dafny/Distributed/Impl/Common/Util.i.dfy
*/
include "machine.s.dfy"

module {:extern "encoding", "github.com/mit-pdos/dafny-jrnl/src/dafny_go/encoding"} IntEncoding
{
    import opened Machine
    import opened ByteSlice

    function method {:axiom} le_enc64(x: uint64): (bs:seq<byte>)
    ensures |bs| == 8
    function method {:axiom} le_dec64(bs: seq<byte>): uint64
    requires |bs| == 8
    lemma {:axiom} lemma_le_enc_dec64(x: uint64)
    ensures le_dec64(le_enc64(x)) == x

    method {:extern} UInt64Put(x: uint64, off: uint64, bytes: Bytes)
    modifies bytes
    requires bytes.Valid() ensures bytes.Valid()
    requires off as nat + 8 <= |bytes.data|
    ensures bytes.data == old(bytes.data[..off as nat] + le_enc64(x) + bytes.data[off as nat+8..])

    method {:extern} UInt64Get(bytes: Bytes, off: uint64)
    returns (x:uint64)
    requires bytes.Valid()
    requires off as nat + 8 <= |bytes.data|
    ensures x == le_dec64(bytes.data[off as nat..off as nat+8])
}
