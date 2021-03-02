/*
Experiment with little-endian encoding of integers.

IronFleet has good code for this at
https://github.com/GLaDOS-Michigan/IronFleet/blob/master/ironfleet/src/Dafny/Distributed/Impl/Common/Util.i.dfy
*/
include "machine.s.dfy"
include "bytes.s.dfy"

module {:extern "encoding", "github.com/mit-pdos/dafny-jrnl/dafny_go/encoding"} IntEncoding
{
    import opened Machine
    import opened ByteSlice

    const u64_bytes: nat := 8
    const u32_bytes: nat := 4

    function method {:axiom} le_enc64(x: uint64): (bs:seq<byte>)
        ensures |bs| == u64_bytes
    function method {:axiom} le_dec64(bs: seq<byte>): uint64
        requires |bs| == u64_bytes
    lemma {:axiom} lemma_le_enc_dec64(x: uint64)
        ensures le_dec64(le_enc64(x)) == x
    lemma {:axiom} lemma_le_dec_enc64(bs: seq<byte>)
        requires |bs| == u64_bytes
        ensures le_enc64(le_dec64(bs)) == bs
    lemma {:axiom} lemma_enc_0()
        ensures le_enc64(0) == [0,0,0,0,0,0,0,0]
    lemma lemma_dec_0()
        ensures le_dec64([0,0,0,0,0,0,0,0]) == 0
    {
        lemma_enc_0();
        lemma_le_enc_dec64(0);
    }

    function method {:axiom} le_enc32(x: uint32): (bs:seq<byte>)
        ensures |bs| == u32_bytes
    function method {:axiom} le_dec32(bs: seq<byte>): uint32
        requires |bs| == u32_bytes
    lemma {:axiom} lemma_le_enc_dec32(x: uint32)
        ensures le_dec32(le_enc32(x)) == x
    lemma {:axiom} lemma_enc_32_0()
        ensures le_enc32(0) == [0,0,0,0]

    method {:extern} UInt64Put(x: uint64, off: uint64, bytes: Bytes)
    modifies bytes
    requires bytes.Valid() ensures bytes.Valid()
    requires off as nat + u64_bytes <= |bytes.data|
    ensures bytes.data == old(bytes.data[..off as nat] + le_enc64(x) + bytes.data[off as nat+u64_bytes..])

    method {:extern} UInt64Get(bytes: Bytes, off: uint64)
    returns (x:uint64)
    requires bytes.Valid()
    requires off as nat + u64_bytes <= |bytes.data|
    ensures x == le_dec64(bytes.data[off as nat..off as nat+u64_bytes])

    method {:extern} UInt32Put(x: uint32, off: uint64, bytes: Bytes)
    modifies bytes
    requires bytes.Valid() ensures bytes.Valid()
    requires off as nat + u32_bytes <= |bytes.data|
    ensures bytes.data == old(bytes.data[..off as nat] + le_enc32(x) + bytes.data[off as nat+u32_bytes..])

    method {:extern} UInt32Get(bytes: Bytes, off: uint64)
    returns (x:uint32)
    requires bytes.Valid()
    requires off as nat + u32_bytes <= |bytes.data|
    ensures x == le_dec32(bytes.data[off as nat..off as nat+u32_bytes])

}
