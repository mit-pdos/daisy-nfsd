include "machine.s.dfy"
include "int.dfy"

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

predicate prefix_of<T>(s1: seq<T>, s2: seq<T>) {
    |s1| <= |s2| && s1 == s2[..|s1|]
}

lemma prefix_of_concat2<T>(s1: seq<T>, s2: seq<T>, s: seq<T>)
requires prefix_of(s1, s2)
ensures prefix_of(s1, s2 + s)
{
}

lemma prefix_of_refl<T>(s: seq<T>)
ensures prefix_of(s, s)
{
}

lemma prefix_of_refl_inv<T>(s1: seq<T>, s2: seq<T>)
requires prefix_of(s1, s2)
requires |s1| == |s2|
ensures s1 == s2
{
}

class {:autocontracts} Encoder
{
    ghost var enc: seq<Encodable>;
    ghost const size: nat;
    var data: array<byte>;
    var off: nat;

    predicate Valid()
    {
        && off <= data.Length
        && seq_encode(enc) == data[..off]
        && data.Length == size
    }

    constructor(size: nat)
    {
        this.data := new byte[size];
        this.off := 0;
        this.enc := [];
        this.size := size;
    }

    function bytes_left(): nat
    requires Valid()
    {
        data.Length-off
    }

    method EncInt(x: uint64)
    requires bytes_left() >= 8
    {
        forall k: nat | 0 <= k < 8 {
            data[off+k] := le_enc64(x)[k];
        }
        assert data[off..off+8] == le_enc64(x);
        off := off + 8;
        enc := enc + [EncUInt64(x)];
        seq_encode_app(old(enc), [EncUInt64(x)]);
    }

    method Finish() returns (bs:array<byte>)
    ensures prefix_of(seq_encode(enc), bs[..])
    ensures bs.Length == size
    {
        return data;
    }
}

class {:autocontracts} Decoder
{
    ghost var enc: seq<Encodable>;
    var data: array<byte>;
    var off: nat;

    predicate Valid()
    {
        && off <= data.Length
        && prefix_of(seq_encode(enc), data[off..])
    }

    constructor {:autocontracts false}
    (data: array<byte>, ghost enc: seq<Encodable>)
    requires prefix_of(seq_encode(enc), data[..])
    ensures Valid() && fresh(Repr - {this, data})
    {
        this.data := data;
        this.off := 0;
        this.enc := enc;
        this.Repr := {this, data};
    }

    lemma prefix_of_app2<T>(s1: seq<T>, s2: seq<T>, n: nat)
    requires prefix_of(s1, s2)
    requires n <= |s1|
    ensures prefix_of(s1[n..], s2[n..])
    {
    }

    method DecInt(ghost x: uint64) returns (x':uint64)
    requires |enc| > 0 && enc[0] == EncUInt64(x)
    ensures x' == x
    ensures enc == old(enc)[1..]
    {
        //assert enc == [enc[0]] + enc[1..];
        //seq_encode_app([enc[0]], enc[1..]);
        //assert data[off..] == data[off..off+8] + data[off+8..];
        //assert |enc_encode(enc[0])| == 8;
        prefix_of_app2(seq_encode(enc), data[off..], 8);
        //assert prefix_of(seq_encode(enc[1..]), data[off+8..]);
        x' := le_dec64(data[off..off+8]);
        lemma_le_enc_dec64(x);
        assert data[off..off+8] == enc_encode(EncUInt64(x));
        off := off + 8;
        enc := enc[1..];
        assert Valid();
    }
}
