include "../machine/int_encoding.s.dfy"
include "../util/marshal.i.dfy"
include "../jrnl/jrnl.s.dfy"

const Acct1: Addr := Addr(513, 0);
const Acct2: Addr := Addr(513, 8*8);

/*
Demo of bank transfer using axiomatized journal API
*/
class Bank
{
    ghost const acct_sum: uint64;
    ghost var acct1: uint64;
    ghost var acct2: uint64;

    var jrnl: Jrnl;

    static method encode_acct(x: uint64) returns (bs:seq<byte>)
    modifies {}
    ensures seq_encode([EncUInt64(x)]) == bs
    {
        var enc := new Encoder(8);
        enc.PutInt(x);
        bs := enc.FinishComplete();
    }

    static method decode_acct(bs:seq<byte>, ghost x: uint64) returns (x': uint64)
    modifies {}
    requires seq_encode([EncUInt64(x)]) == bs
    ensures x' == x
    {
        var dec := new Decoder();
        dec.Init(bs, [EncUInt64(x)]);
        x' := dec.GetInt(x);
    }

    // NOTE: unused, but an example of how painful helper methods are
    static method zeroAccount(jrnl: Jrnl, acct: Addr)
    requires jrnl.Valid() ensures jrnl.Valid()
    requires jrnl.has_kind(acct, KindUInt64)
    modifies jrnl
    ensures jrnl.data == old(jrnl.data)[acct := seq_encode([EncUInt64(0)])]
    {
        var data := encode_acct(0);
        jrnl.Write(acct, data);
    }

    constructor()
    ensures this.Valid()
    ensures acct1 == 100 && acct2 == 0
    {
        // BUG: we can't actually use the constant because then Dafny makes the type
        // of the map display expression map<int,int>.
        assert 6 == KindUInt64;
        var kinds: map<Blkno, Kind> := map[513:=6];
        var jrnl := new Jrnl(kinds);
        var hundred_acct := encode_acct(100);
        var zero_acct := encode_acct(0);
        jrnl.Write(Acct1, hundred_acct);
        jrnl.Write(Acct2, zero_acct);
        this.jrnl := jrnl;

        acct1 := 100;
        acct2 := 0;
        acct_sum := 100;
    }

    predicate Valid()
    reads this, jrnl, jrnl.Repr
    {
        && jrnl.Valid()
        && Acct1 in jrnl.domain
        && Acct2 in jrnl.domain
        && jrnl.size(Acct1) == 64
        && jrnl.size(Acct2) == 64
        && jrnl.data[Acct1] == seq_encode([EncUInt64(acct1)])
        && jrnl.data[Acct2] == seq_encode([EncUInt64(acct2)])
        && acct_sum == acct1 + acct2
    }

    // NOTE: this should be interpreted as the body of a transaction, which
    // needs to be surrounded with code to check for errors and abort
    method transfer()
    requires Valid() ensures Valid()
    modifies {this,jrnl}
    requires 0 < acct1
    requires acct2+1 < 0x1_0000_0000_0000_000
    ensures acct1 == old(acct1) - 1
    ensures acct2 == old(acct2) + 1
    {
        var x := jrnl.Read(Acct1, 64);
        var acct1_val := decode_acct(x.obj, acct1);
        x.obj := encode_acct(acct1_val-1);
        x.SetDirty();
        acct1 := acct1 - 1;

        x := jrnl.Read(Acct2, 64);
        var acct2_val := decode_acct(x.obj, acct2);
        x.obj := encode_acct(acct2_val+1);
        x.SetDirty();
        acct2 := acct2 + 1;
    }

    // this is kind of silly but it gets the point across (without requiring the
    // reader to understand Valid())
    method audit() returns (b:bool)
    modifies {}
    requires Valid()
    ensures b == (acct1 + acct2 == acct_sum)
    {
        return true;
    }
}
