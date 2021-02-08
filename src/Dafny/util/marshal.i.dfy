include "../machine/int_encoding.s.dfy"
include "../util/collections.dfy"

module Marshal
{

import opened Machine
import opened IntEncoding
import opened ByteSlice
import opened Collections

datatype Encodable = EncUInt64(x:uint64) | EncUInt32(y:uint32)

function enc_encode(e: Encodable): seq<byte>
{
    match e
    case EncUInt64(x) => le_enc64(x)
    case EncUInt32(x) => le_enc32(x)
}

function seq_encode(es: seq<Encodable>): seq<byte>
decreases es
{
    if es == [] then []
    else enc_encode(es[0]) + seq_encode(es[1..])
}

lemma seq_encode_concat(es: seq<Encodable>)
    ensures seq_encode(es) == C.concat(seq_fmap(enc_encode, es))
{}

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

class Encoder
{
    ghost var enc: seq<Encodable>;
    ghost const size: nat;
    const data: Bytes;
    var off: uint64;
    const Repr: set<object>;

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
}

}
