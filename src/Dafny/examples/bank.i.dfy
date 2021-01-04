include "../machine/int_encoding.s.dfy"
include "../util/marshal.i.dfy"
include "../jrnl/jrnl.s.dfy"

/*
Demo of bank transfer using axiomatized journal API
*/
class Bank
{
    ghost const acct_sum: nat;
    ghost var accts: seq<uint64>;

    var jrnl: Jrnl;

    static function method Acct(n: nat): (a:Addr)
    requires n < 512
    {
        Addr(513, n*64)
    }

    static predicate acct_val(jrnl: Jrnl, acct: Addr, val: uint64)
    reads jrnl
    requires jrnl.Valid()
    requires acct in jrnl.domain
    {
        jrnl.data[acct] == seq_encode([EncUInt64(val)])
    }

    predicate Valid()
    reads this, jrnl
    {
        && jrnl.Valid()
        && |accts| == 512
        && forall n: nat :: n < 512 ==>
            (var acct := Acct(n);
             && acct in jrnl.domain
             && jrnl.size(acct) == 64
             && acct_val(jrnl, acct, accts[n]))
        && acct_sum == sum_nat(accts)
    }

    static method encode_acct(x: uint64) returns (bs:seq<byte>)
    ensures seq_encode([EncUInt64(x)]) == bs
    {
        var enc := new Encoder(8);
        enc.PutInt(x);
        bs := enc.FinishComplete();
    }

    static method decode_acct(bs:seq<byte>, ghost x: uint64) returns (x': uint64)
    requires seq_encode([EncUInt64(x)]) == bs
    ensures x' == x
    {
        var dec := new Decoder();
        dec.Init(bs, [EncUInt64(x)]);
        x' := dec.GetInt(x);
    }

    constructor(init_bal: uint64)
    ensures Valid()
    ensures forall n: nat:: n < 512 ==> accts[n] == init_bal
    ensures acct_sum == 512*init_bal
    {
        // BUG: we can't actually use the constant because then Dafny makes the type
        // of the map display expression map<int,int>.
        assert 6 == KindUInt64;
        var kinds: map<Blkno, Kind> := map[513:=6];
        var jrnl := new Jrnl(kinds);

        assert forall n: nat :: n < 512 ==>
            (var acct := Acct(n);
             && acct in jrnl.domain
             && jrnl.size(acct) == 64);

        var init_acct := encode_acct(init_bal);
        var n := 0;
        while n < 512
        invariant jrnl.Valid()
        invariant forall k:: 0 <= k < n ==> acct_val(jrnl, Acct(k), init_bal)
        {
            jrnl.Write(Acct(n), init_acct);
            n := n + 1;
        }

        this.jrnl := jrnl;

        // NOTE: this was really annoying to figure out - turns out needed the
        // accounts to be a repeat of nats instead of uint64 (hence the extra
        // let binding and type annotations)
        var new_accts: seq<nat> := repeat(init_bal as nat, 512);
        sum_repeat(init_bal, 512);
        accts := new_accts;
        acct_sum := 512*init_bal;
    }

    // NOTE: this should be interpreted as the body of a transaction, which
    // needs to be surrounded with code to check for errors and abort
    method transfer(acct1: nat, acct2: nat)
    requires Valid() ensures Valid()
    modifies {this,jrnl}
    requires acct1 < 512 && acct2 < 512 && acct1 != acct2
    requires 0 < accts[acct1]
    requires accts[acct2] < 0x1_0000_0000_0000_000-1
    ensures accts == old(accts[acct1:=accts[acct1]-1][acct2:=accts[acct2]+1])
    {
        var x := jrnl.Read(Acct(acct1), 64);
        var acct1_val := decode_acct(x.obj, accts[acct1]);
        x.obj := encode_acct(acct1_val-1);
        x.SetDirty();
        sum_update(accts, acct1, acct1_val-1);
        accts := accts[acct1:=acct1_val-1];

        x := jrnl.Read(Acct(acct2), 64);
        var acct2_val := decode_acct(x.obj, accts[acct2]);
        x.obj := encode_acct(acct2_val+1);
        x.SetDirty();
        sum_update(accts, acct2, acct2_val+1);
        accts := accts[acct2:=acct2_val+1];

    }

    // this is kind of silly but it gets the point across (without requiring the
    // reader to understand Valid())
    method audit() returns (b:bool)
    modifies {}
    requires Valid()
    ensures b == (sum_nat(accts) == acct_sum)
    {
        return true;
    }
}
