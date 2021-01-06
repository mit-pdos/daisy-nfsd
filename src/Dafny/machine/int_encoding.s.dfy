/*
Experiment with little-endian encoding of integers.

IronFleet has good code for this at
https://github.com/GLaDOS-Michigan/IronFleet/blob/master/ironfleet/src/Dafny/Distributed/Impl/Common/Util.i.dfy
*/
include "machine.s.dfy"

module IntEncoding
{

import opened Machine
import opened bytes

function le_enc16(x: bv16): (bs:seq<byte>)
ensures |bs| == 2
{
    var b0: byte := (x & 0xFF) as byte;
    var b1: byte := (x >> 8) as byte;
    [b0, b1]
}

function le_dec16(x: seq<byte>): bv16
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

function method {:axiom} le_enc64(x: uint64): (bs:seq<byte>)
ensures |bs| == 8
function method {:axiom} le_dec64(bs: seq<byte>): uint64
requires |bs| == 8
lemma {:axiom} lemma_le_enc_dec64(x: uint64)
ensures le_dec64(le_enc64(x)) == x

lemma split_at_last<T>(xs: seq<T>, k: nat)
requires 1 <= k < |xs|
ensures xs[..k] == xs[..k-1] + [xs[k-1]]
{}

lemma singleton_eq<T>(x1: T, x2: T)
requires x1 == x2
ensures [x1] == [x2]
{}

method {:extern} UInt64Put(x: uint64, off: uint64, bytes: Bytes)
modifies bytes
requires bytes.Valid() ensures bytes.Valid()
requires off as nat + 8 <= |bytes.data()|
ensures bytes.data() == old(bytes.data()[..off as nat] + le_enc64(x) + bytes.data()[off as nat+8..])

method {:extern} UInt64Get(bytes: Bytes, off: uint64)
returns (x:uint64)
requires bytes.Valid()
requires off as nat + 8 <= |bytes.data()|
ensures x == le_dec64(bytes.data()[off as nat..off as nat+8])


}
