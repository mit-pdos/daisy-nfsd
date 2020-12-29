/*
Experiment with little-endian encoding of integers.

IronFleet has good code for this at
https://github.com/GLaDOS-Michigan/IronFleet/blob/master/ironfleet/src/Dafny/Distributed/Impl/Common/Util.i.dfy
*/

function le_enc16(x: bv16): (bs:seq<bv8>)
ensures |bs| == 2
{
    var b0: bv8 := (x & 0xFF) as bv8;
    var b1: bv8 := (x >> 8) as bv8;
    [b0, b1]
}

function le_dec16(x: seq<bv8>): bv16
requires |x| == 2
{
    (x[0] as bv16) |
    ((x[1] << 8) as bv16)
}

// this turns out to be hard
/*
lemma le_roundtrip16(x: bv16)
ensures le_dec16(le_enc16(x)) == x
{
}
*/

function {:axiom} le_enc64(x: bv64): (bs:seq<bv8>)
ensures |bs| == 8
function {:axiom} le_dec64(bs: seq<bv8>): bv64
requires |bs| == 8
lemma {:axiom} lemma_le_enc_dec64(x: bv64)
ensures le_dec64(le_enc64(x)) == x
