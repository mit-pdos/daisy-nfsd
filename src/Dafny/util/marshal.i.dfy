include "../machine/int_encoding.s.dfy"
include "../util/collections.dfy"

module Marshal
{

import opened Machine
import opened IntEncoding
import opened ByteSlice
import opened Collections

datatype Encodable = EncUInt64(x:uint64) | EncUInt32(y:uint32) | EncBytes(bs: seq<byte>)

function EncByte(b: byte): Encodable { EncBytes([b]) }

function enc_encode(e: Encodable): seq<byte>
{
    match e
    case EncUInt64(x) => le_enc64(x)
    case EncUInt32(x) => le_enc32(x)
    case EncBytes(bs) => bs
}

function seq_encode(es: seq<Encodable>): seq<byte>
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
function encUInt64(x: uint64): Encodable { EncUInt64(x) }

function seq_enc_uint64(xs: seq<uint64>): seq<byte>
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

function decode_uint64(bs: seq<byte>): (x:uint64)
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

function decode_uint64_seq(bs: seq<byte>): (es: seq<uint64>)
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

class Encoder
{
    ghost var enc: seq<Encodable>;
    ghost const size: nat;
    const data: Bytes;
    var off: uint64;
    ghost const Repr: set<object>;

    predicate {:opaque} Valid()
        reads Repr
    {
        && Repr == {this, data}
        && data.Valid()
        && off as nat <= data.Len() as nat
        && seq_encode(enc) == data.data[..off]
        && |data.data| == size
        && data.data[off..] == repeat(0 as byte, size-off as nat)
    }

    constructor(size: uint64)
    ensures Valid()
    ensures enc == []
    ensures this.size == size as nat
    ensures bytes_left() == this.size
    ensures fresh(data)
    {
        var bs := NewBytes(size);
        this.data := bs;
        this.off := 0;
        this.enc := [];
        this.size := size as nat;
        this.Repr := {this, data};
        new;
        reveal_Valid();
    }

    function bytes_left(): nat
        reads Repr
        requires Valid()
    {
        reveal_Valid();
        |data.data|-(off as nat)
    }

    method PutInt(x: uint64)
    modifies Repr
    requires Valid() ensures Valid()
    requires bytes_left() >= 8
    ensures bytes_left() == old(bytes_left()) - 8
    ensures enc == old(enc) + [EncUInt64(x)]
    {
        UInt64Put(x, off, data);
        assert data.data[off..off+8] == le_enc64(x);
        off := off + 8;
        enc := enc + [EncUInt64(x)];
        seq_encode_app(old(enc), [EncUInt64(x)]);
    }

    method PutInt32(x: uint32)
    modifies Repr
    requires Valid() ensures Valid()
    requires bytes_left() >= 4
    ensures bytes_left() == old(bytes_left()) - 4
    ensures enc == old(enc) + [EncUInt32(x)]
    {
        UInt32Put(x, off, data);
        assert data.data[off..off+4] == le_enc32(x);
        off := off + 4;
        enc := enc + [EncUInt32(x)];
        seq_encode_app(old(enc), [EncUInt32(x)]);
    }

    method PutByte(b: byte)
    modifies Repr
    requires Valid() ensures Valid()
    requires bytes_left() >= 1
    ensures bytes_left() == old(bytes_left()) - 1
    ensures enc == old(enc) + [EncByte(b)]
    {
        data.Set(off, b);
        off := off + 1;
        enc := enc + [EncByte(b)];
        seq_encode_app(old(enc), [EncByte(b)]);
    }

    method PutBytes(bs: Bytes)
        modifies Repr
        requires bs !in Repr
        requires Valid() ensures Valid()
        requires bs.Valid()
        requires bytes_left() >= |bs.data|
        ensures bytes_left() == old(bytes_left()) - |bs.data|
        ensures enc == old(enc) + [EncBytes(bs.data)]
    {
        data.CopyTo(off, bs);
        off := off + bs.Len();
        enc := enc + [EncBytes(bs.data)];
        seq_encode_app(old(enc), [EncBytes(bs.data)]);
    }

    method PutByteSeq(bs: seq<byte>)
        modifies Repr
        requires Valid() ensures Valid()
        requires bytes_left() >= |bs|
        ensures bytes_left() == old(bytes_left()) - |bs|
        ensures enc == old(enc) + [EncBytes(bs)]
    {
        var i := 0;
        while i < |bs|
            modifies data
            invariant 0 <= i <= |bs|
            invariant enc == old(enc)
            invariant off == old(off)
            invariant data.data == C.splice(old(data.data), off as nat, bs[..i])
        {
            ghost var data0 := data.data;
            data.Set(off + i as uint64, bs[i]);
            i := i + 1;
        }
        off := off + |bs| as uint64;
        enc := enc + [EncBytes(bs)];
        seq_encode_app(old(enc), [EncBytes(bs)]);
    }

    method PutInts(xs: seq<uint64>)
        modifies Repr
        requires Valid() ensures Valid()
        requires bytes_left() >= 8*|xs|
        ensures bytes_left() == old(bytes_left()) - 8*|xs|
        ensures enc == old(enc) + seq_fmap(encUInt64, xs)
    {
        var len := |xs| as uint64;
        var i: uint64 := 0;
        while i < len
            invariant i as nat <= |xs|
            invariant Valid()
            invariant bytes_left() == old(bytes_left()) - 8*(i as nat)
            invariant enc == old(enc + seq_fmap(encUInt64, xs[..i]))
        {
            PutInt(xs[i as nat]);
            i := i + 1;
        }
        assert xs[..|xs|] == xs;
    }

    method Finish() returns (bs:Bytes)
    requires Valid() ensures Valid()
    ensures bs.Valid()
    ensures bs.data == seq_encode(enc) + repeat(0 as byte, bytes_left())
    ensures |bs.data| == size
    ensures bs == data
    {
        reveal_Valid();
        return data;
    }

    lemma is_complete()
        requires Valid()
        requires bytes_left() == 0
        ensures repeat(0 as byte, bytes_left()) == []
    {}
}

class Decoder
{
    ghost var enc: seq<Encodable>;
    const data: Bytes;
    var off: uint64;

    predicate Valid()
        reads this, data
    {
        && data.Valid()
        && off as nat <= |data.data|
        && prefix_of(seq_encode(enc), data.data[off..])
    }

    lemma decode_peel1(e: Encodable)
        requires Valid()
        requires |enc| > 0 && enc[0] == e
        ensures enc_encode(e) == data.data[off..off as nat + |enc_encode(e)|]
        ensures prefix_of(seq_encode(enc[1..]), data.data[off as nat+|enc_encode(e)|..])
    {
        // not entirely sure why this works, seems to trigger something useful
        prefix_of_app2(seq_encode(enc), data.data[off..], |enc_encode(e)|);
    }

    constructor Init(data: Bytes, ghost enc: seq<Encodable>)
    requires data.Valid()
    requires prefix_of(seq_encode(enc), data.data)
    ensures Valid()
    ensures this.enc == enc
    ensures this.data == data
    {
        this.data := data;
        this.off := 0;
        this.enc := enc;
    }

    method GetInt(ghost x: uint64) returns (x':uint64)
    modifies this
    requires Valid() ensures Valid()
    requires |enc| > 0 && enc[0] == EncUInt64(x)
    ensures x' == x
    ensures enc == old(enc)[1..]
    {
        //assert enc == [enc[0]] + enc[1..];
        //seq_encode_app([enc[0]], enc[1..]);
        //assert data[off..] == data[off..off+8] + data[off+8..];
        //assert |enc_encode(enc[0])| == 8;
        //prefix_of_app2(seq_encode(enc), data.data[off..], 8);
        //assert prefix_of(seq_encode(enc[1..]), data[off+8..]);


        decode_peel1(EncUInt64(x));
        x' := UInt64Get(data, off);
        assert x == x' by {
            lemma_le_enc_dec64(x);
        }
        off := off + 8;
        enc := enc[1..];
    }

    method GetInt32(ghost x: uint32) returns (x': uint32)
        modifies this
        requires Valid() ensures Valid()
        requires |enc| > 0 && enc[0] == EncUInt32(x)
        ensures x' == x
        ensures enc == old(enc[1..])
    {
        decode_peel1(EncUInt32(x));
        x' := UInt32Get(data, off);
        assert x == x' by {
            lemma_le_enc_dec32(x);
        }
        off := off + 4;
        enc := enc[1..];
    }

    method GetByte(ghost b: byte) returns (b': byte)
        modifies this
        requires Valid() ensures Valid()
        requires |enc| > 0 && enc[0] == EncByte(b)
        ensures b' == b
        ensures enc == old(enc[1..])
    {
        decode_peel1(EncByte(b));
        b' := data.Get(off);
        off := off + 1;
        enc := enc[1..];
    }

    method GetBytes(len: uint64, ghost bs: seq<byte>) returns (bs': Bytes)
        modifies this
        requires Valid() ensures Valid()
        requires |enc| > 0 && enc[0] == EncBytes(bs)
        requires |bs| == len as nat
        ensures fresh(bs') && bs'.Valid() && bs'.data == bs
        ensures enc == old(enc[1..])
    {
        decode_peel1(EncBytes(bs));
        bs' := NewBytes(len);
        bs'.CopyFrom(this.data, off, len);
        off := off + len;
        enc := enc[1..];
    }

    method GetByteSeq(len: uint64, ghost bs: seq<byte>) returns (bs':seq<byte>)
        modifies this
        requires Valid() ensures Valid()
        requires |enc| > 0 && enc[0] == EncBytes(bs)
        requires |bs| == len as nat
        ensures bs' == bs
        ensures enc == old(enc[1..])
    {
        decode_peel1(EncBytes(bs));
        bs' := [];
        var i: uint64 := 0;
        while i < len
            modifies {}
            invariant 0 <= i as nat <= len as nat
            invariant bs' == bs[..i]
        {
            var b := data.Get(off + i);
            bs' := bs' + [b];
            i := i + 1;
        }
        assert bs[..len as nat] == bs;
        off := off + len;
        enc := enc[1..];
    }

    method GetInts(num: uint64, ghost xs: seq<uint64>) returns (xs': seq<uint64>)
        modifies this
        requires Valid() ensures Valid()
        requires num as nat == |xs|
        requires |enc| >= num as nat && enc[..num as nat] == seq_fmap(encUInt64, xs)
        ensures xs' == xs
        ensures enc == old(enc[|xs|..])
    {
        var num_ := num as nat;
        var xs_a := new uint64[num_];
        var i: uint64 := 0;
        while i < num
            invariant Valid()
            invariant i as nat <= num_
            invariant xs_a.Length == num_
            invariant xs_a[..i] == xs[..i]
            invariant enc == old(enc[i..])
        {
            xs_a[i as nat] := GetInt(xs[i]);
            i := i + 1;
        }
        return xs_a[..];
    }
}

}
