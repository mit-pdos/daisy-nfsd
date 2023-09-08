include "../machine/int_encoding.s.dfy"
include "../util/collections.dfy"

module Marshal
{

import opened Machine
import opened IntEncoding
import opened ByteSlice
import opened Collections

method UInt64Decode(bs: Bytes, off: uint64, ghost x: uint64) returns (x': uint64)
    requires off as nat + 8 <= |bs.data|
    requires bs.Valid()
    requires bs.data[off as nat..off as nat + 8] == IntEncoding.le_enc64(x)
    ensures x' == x
{
    IntEncoding.lemma_le_enc_dec64(x);
    x' := IntEncoding.UInt64Get(bs, off);
}

method UInt32Decode(bs: Bytes, off: uint64, ghost x: uint32) returns (x': uint32)
    requires off as nat + 4 <= |bs.data|
    requires bs.Valid()
    requires bs.data[off as nat..off as nat + 4] == IntEncoding.le_enc32(x)
    ensures x' == x
{
    IntEncoding.lemma_le_enc_dec32(x);
    x' := IntEncoding.UInt32Get(bs, off);
}

datatype Encodable = EncUInt64(x:uint64) | EncUInt32(y:uint32) | EncBytes(bs: seq<byte>)

ghost function EncByte(b: byte): Encodable { EncBytes([b]) }

ghost function enc_encode(e: Encodable): seq<byte>
{
    match e
    case EncUInt64(x) => le_enc64(x)
    case EncUInt32(x) => le_enc32(x)
    case EncBytes(bs) => bs
}

ghost function seq_encode(es: seq<Encodable>): seq<byte>
decreases es
{
    if es == [] then []
    else enc_encode(es[0]) + seq_encode(es[1..])
}

lemma seq_encode_unfold(es: seq<Encodable>)
    requires 0 < |es|
    ensures seq_encode(es) == enc_encode(es[0]) + seq_encode(es[1..])
{}

lemma seq_encode_concat(es: seq<Encodable>)
    ensures seq_encode(es) == C.concat(seq_fmap(enc_encode, es))
{
    reveal_seq_fmap();
}

lemma {:induction es1} seq_encode_app(es1: seq<Encodable>, es2: seq<Encodable>)
ensures seq_encode(es1 + es2) == seq_encode(es1) + seq_encode(es2)
{
    if es1 == [] {
        assert es1 + es2 == es2;
    } else {
        //assert seq_encode([es1[0]]) == enc_encode(es1[0]);
        //assert seq_encode(es1[1..] + es2) == seq_encode(es1[1..] + es2);
        //assert seq_encode(es1) == enc_encode(es1[0]) + seq_encode(es1[1..]);
        assert es1 + es2 == [es1[0]] + es1[1..] + es2;
        assert ([es1[0]] + es1[1..] + es2)[0] == es1[0];
        // NOTE(tej): discovered with a calc statement
        assert ([es1[0]] + es1[1..] + es2)[1..] == es1[1..] + es2;
    }
}

// BUG: Dafny cannot reason about equality of the lambda x => EncUInt64(x)
// without a global definition
ghost function encUInt64(x: uint64): Encodable { EncUInt64(x) }

ghost function seq_enc_uint64(xs: seq<uint64>): seq<byte>
{
    seq_encode(seq_fmap(encUInt64, xs))
}

lemma enc_uint64_len(xs: seq<uint64>)
ensures |seq_enc_uint64(xs)| == 8*|xs|
{
    seq_encode_concat(seq_fmap(encUInt64, xs));
    C.concat_homogeneous_len(seq_fmap(enc_encode, seq_fmap(encUInt64, xs)), 8);
}

lemma zero_encode_seq_uint64_helper(n: nat)
  ensures seq_enc_uint64(C.repeat(0 as uint64, n)) == seq_encode(C.repeat(EncUInt64(0), n))
{
  C.seq_ext_eq(C.seq_fmap(encUInt64, C.repeat(0 as uint64, n)), C.repeat(EncUInt64(0), n));
}

lemma zero_encode_as_repeat()
  ensures enc_encode(EncUInt64(0)) == C.repeat(0 as byte, 8)
{
  IntEncoding.lemma_enc_0();
}

lemma zero_encode_seq_uint64(n: nat)
  ensures seq_enc_uint64(repeat(0 as uint64, n)) == repeat(0 as byte, 8*n)
{
  var zero_encs := repeat(EncUInt64(0), n);
  calc {
    seq_enc_uint64(repeat(0 as uint64, n));
    { zero_encode_seq_uint64_helper(n);
      seq_encode_concat(zero_encs); }
    concat(seq_fmap(enc_encode, zero_encs));
    { seq_ext_eq(seq_fmap(enc_encode, zero_encs), repeat(enc_encode(EncUInt64(0)), n)); }
    concat(repeat(enc_encode(EncUInt64(0)), n));
    { zero_encode_as_repeat(); }
    concat(repeat(repeat(0 as byte, 8), n));
    { var s := repeat(repeat(0 as byte, 8), n);
      concat_homogeneous_spec_alt(s, 8);
      seq_ext_eq(concat(s), repeat(0 as byte, 8*n));
    }
    repeat(0 as byte, 8*n);
  }
}

ghost function decode_uint64(bs: seq<byte>): (x:uint64)
    requires |bs| == u64_bytes
    ensures enc_encode(EncUInt64(x)) == bs
{
    lemma_le_dec_enc64(bs);
    le_dec64(bs)
}

lemma decode_encode_uint64(x: uint64)
    ensures decode_uint64(enc_encode(EncUInt64(x))) == x
{
    lemma_le_enc_dec64(x);
}

ghost function decode_uint64_seq(bs: seq<byte>): (es: seq<uint64>)
    requires |bs| % 8 == 0
    ensures seq_encode(seq_fmap(encUInt64, es)) == bs
    ensures |es| == |bs|/8
{
    if bs == [] then []
    else (
        var es := [decode_uint64(bs[..8])] + decode_uint64_seq(bs[8..]);
        assert seq_fmap(encUInt64, es) == [EncUInt64(es[0])] + seq_fmap(encUInt64, es[1..]);
        es
    )
}

lemma decode_encode_uint64_seq_id(es: seq<uint64>)
    ensures (enc_uint64_len(es);
            decode_uint64_seq(seq_encode(seq_fmap(encUInt64, es))) == es)
{
    if es == [] { return; }
    decode_encode_uint64(es[0]);
    decode_encode_uint64_seq_id(es[1..]);
    enc_uint64_len(es[1..]);
    assert seq_fmap(encUInt64, es[1..]) == seq_fmap(encUInt64, es)[1..];
    assert seq_encode(seq_fmap(encUInt64, es[1..])) == seq_encode(seq_fmap(encUInt64, es))[8..];
}

ghost function decode_uint64_seq_one(bs: seq<byte>, k: nat): uint64
    requires |bs| % 8 == 0
    requires k*8 < |bs|
{
    decode_uint64(bs[k*8..(k+1)*8])
}

lemma decode_uint64_seq_one_spec(bs: seq<byte>, k: nat)
    requires |bs| % 8 == 0
    requires k*8 < |bs|
    ensures decode_uint64_seq_one(bs, k) == decode_uint64_seq(bs)[k]
{
    if bs == [] { return; }
    if k == 0 { return; }
    decode_uint64_seq_one_spec(bs[8..], k-1);
    calc {
        decode_uint64_seq(bs)[k];
        decode_uint64_seq(bs[8..])[k-1];
        decode_uint64_seq_one(bs[8..], k-1);
        { assert bs[8..][(k-1)*8 .. (k-1+1)*8] == bs[k*8..(k+1)*8]; }
        decode_uint64_seq_one(bs, k);
    }
}

lemma decode_uint64_seq_pointwise(bs: seq<byte>)
    requires |bs| % 8 == 0
    ensures decode_uint64_seq(bs) ==
            seq(|bs|/8, (k:nat) requires k < |bs|/8 => decode_uint64_seq_one(bs, k))
{
    forall k:nat | k < |bs|/8
        ensures decode_uint64_seq(bs)[k] == decode_uint64_seq_one(bs, k)
    {
        decode_uint64_seq_one_spec(bs, k);
    }
}

lemma decode_uint64_seq_modify_one(bs: seq<byte>, k: nat, x: uint64)
    requires |bs| % 8 == 0
    requires k*8 < |bs|
    ensures decode_uint64_seq(C.splice(bs, k*8, le_enc64(x))) ==
            decode_uint64_seq(bs)[k := x]
{
    var s1 := decode_uint64_seq(C.splice(bs, k*8, le_enc64(x)));
    var s2 := decode_uint64_seq(bs)[k := x];
    assert s1[k] == x by {
        decode_uint64_seq_one_spec(C.splice(bs, k*8, le_enc64(x)), k);
        lemma_le_enc_dec64(x);
    }
    var k0 := k;
    forall k: nat | k < |bs|/8
        ensures s1[k] == s2[k]
    {
        if k == k0 { }
        else {
            decode_uint64_seq_one_spec(C.splice(bs, k0*8, le_enc64(x)), k);
            decode_uint64_seq_one_spec(bs, k);
            assert C.splice(bs, k0*8, le_enc64(x))[k*8..(k+1)*8] == bs[k*8..(k+1)*8];
        }
    }
    assert s1 == s2;
}

}
