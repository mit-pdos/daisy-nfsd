include "../machine/int_encoding.s.dfy"
include "../util/collections.dfy"

module Marshal
{

import opened Machine
import opened IntEncoding
import opened ByteSlice
import opened Collections

datatype Encodable = EncUInt64(x:uint64)

function enc_encode(e: Encodable): seq<byte>
{
    match e
    case EncUInt64(x) => le_enc64(x)
}

function seq_encode(es: seq<Encodable>): seq<byte>
decreases es
{
    if es == [] then []
    else enc_encode(es[0]) + seq_encode(es[1..])
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

class {:autocontracts} Encoder
{
    ghost var enc: seq<Encodable>;
    ghost const size: nat;
    const data: Bytes;
    var off: uint64;

    predicate Valid()
    {
        && data.Valid()
        && off as nat <= data.Len() as nat
        && seq_encode(enc) == data.data[..off]
        && |data.data| == size
    }

    constructor(size: uint64)
    ensures enc == []
    ensures this.size == size as nat
    ensures bytes_left() == this.size
    {
        var bs := NewBytes(size);
        this.data := bs;
        this.off := 0;
        this.enc := [];
        this.size := size as nat;
    }

    function bytes_left(): nat
    {
        |data.data|-(off as nat)
    }

    method PutInt(x: uint64)
    modifies this, data
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

    method Finish() returns (bs:Bytes)
    ensures bs.Valid()
    ensures prefix_of(seq_encode(enc), bs.data)
    ensures |bs.data| == size
    ensures bs == data
    {
        return data;
    }

    // Exactly the same as Finish but with a simpler spec if the encoder has
    // been completely used
    method FinishComplete() returns (bs:Bytes)
    requires bytes_left() == 0
    ensures bs.Valid()
    ensures seq_encode(enc) == bs.data
    ensures |bs.data| == size
    ensures bs == data
    {
        return data;
    }
}

class Decoder
{
    ghost var enc: seq<Encodable>;
    var data: Bytes;
    var off: uint64;

    predicate Valid()
        reads this, data
    {
        && data.Valid()
        && off as nat <= |data.data|
        && prefix_of(seq_encode(enc), data.data[off..])
    }

    constructor()
    {
        // FIXME: dummy assignment because of "definite assignment rules"
        var bs := NewBytes(0);
        data := bs;
    }

    // not a constructor due to https://github.com/dafny-lang/dafny/issues/374
    method Init(data: Bytes, ghost enc: seq<Encodable>)
    modifies this
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
    ensures data == old(data)
    {
        //assert enc == [enc[0]] + enc[1..];
        //seq_encode_app([enc[0]], enc[1..]);
        //assert data[off..] == data[off..off+8] + data[off+8..];
        //assert |enc_encode(enc[0])| == 8;
        prefix_of_app2(seq_encode(enc), data.data[off..], 8);
        //assert prefix_of(seq_encode(enc[1..]), data[off+8..]);
        x' := UInt64Get(data, off);
        lemma_le_enc_dec64(x);
        assert data.data[off..off+8] == enc_encode(EncUInt64(x));
        off := off + 8;
        enc := enc[1..];
        assert Valid();
    }
}

}
