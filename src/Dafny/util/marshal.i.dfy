include "../machine/machine_s.dfy"
include "../machine/int_encoding.s.dfy"
include "../util/collections.dfy"

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
    var data: array<byte>;
    var off: nat;

    predicate Valid()
    {
        && off <= data.Length
        && seq_encode(enc) == data[..off]
        && data.Length == size
    }

    constructor(size: nat)
    ensures enc == []
    ensures bytes_left() == size
    {
        this.data := new byte[size];
        this.off := 0;
        this.enc := [];
        this.size := size;
    }

    function bytes_left(): nat
    {
        data.Length-off
    }

    method PutInt(x: uint64)
    requires bytes_left() >= 8
    ensures bytes_left() == old(bytes_left()) - 8
    ensures enc == old(enc) + [EncUInt64(x)]
    {
        forall k: nat | 0 <= k < 8 {
            data[off+k] := le_enc64(x)[k];
        }
        assert data[off..off+8] == le_enc64(x);
        off := off + 8;
        enc := enc + [EncUInt64(x)];
        seq_encode_app(old(enc), [EncUInt64(x)]);
    }

    method Finish() returns (bs:seq<byte>)
    ensures prefix_of(seq_encode(enc), bs)
    ensures |bs| == size
    {
        return data[..];
    }

    method FinishComplete() returns (bs:seq<byte>)
    requires bytes_left() == 0
    ensures seq_encode(enc) == bs
    ensures |bs| == size
    {
        return data[..];
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

    constructor {:autocontracts false}()
    {
    }

    // not a constructor due to https://github.com/dafny-lang/dafny/issues/374
    method {:autocontracts false} Init(data: seq<byte>, ghost enc: seq<Encodable>)
    modifies this
    requires prefix_of(seq_encode(enc), data)
    ensures Valid()
    ensures fresh(Repr - {this})
    ensures this.enc == enc
    {
        var mut_data := new byte[|data|];
        forall i:nat | i < |data| {
            mut_data[i] := data[i];
        }
        this.data := mut_data;
        this.off := 0;
        this.enc := enc;
        this.Repr := {this, mut_data};
    }

    method GetInt(ghost x: uint64) returns (x':uint64)
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
