include "../util/marshal.i.dfy"
include "../jrnl/jrnl.s.dfy"

module Bank {

import opened Machine
import opened ByteSlice
import opened JrnlSpec
import opened Kinds
import opened Marshal
import opened Collections

/*
Demo of bank transfer using axiomatized journal API
*/
class Bank
{
    ghost const acct_sum: nat;
    ghost var accts: seq<nat>;

    var jrnl: Jrnl;

    static function method Acct(n: nat): (a:Addr)
    requires n < 512
    {
        Addr(513, n*64)
    }

    static predicate acct_val(jrnl: Jrnl, acct: Addr, val: nat)
    reads jrnl
    requires jrnl.Valid()
    requires acct in jrnl.domain
    {
        && val < 0x1_0000_0000_0000_0000
        && jrnl.data[acct] == ObjData(seq_encode([EncUInt64(val as uint64)]))
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
             && accts[n] < 0x1_0000_0000_0000_0000
             && acct_val(jrnl, acct, accts[n]))
        && acct_sum == sum_nat(accts)
    }

    static method encode_acct(x: uint64) returns (bs:Bytes)
    ensures fresh(bs)
    ensures bs.Valid()
    ensures seq_encode([EncUInt64(x)]) == bs.data
    {
        var enc := new Encoder(8);
        enc.PutInt(x);
        bs := enc.FinishComplete();
    }

    static method decode_acct(bs:Bytes, ghost x: nat) returns (x': uint64)
    requires x < 0x1_0000_0000_0000_0000
    requires bs.Valid()
    requires seq_encode([EncUInt64(x as uint64)]) == bs.data
    ensures x' as nat == x
    {
        var dec := new Decoder();
        dec.Init(bs, [EncUInt64(x as uint64)]);
        x' := dec.GetInt(x as uint64);
    }

    constructor(init_bal: uint64)
    ensures Valid()
    ensures forall n: nat:: n < 512 ==> accts[n] == init_bal as nat
    ensures acct_sum == 512*(init_bal as nat)
    {
        // BUG: we can't actually use the constant because then Dafny makes the type
        // of the map display expression map<int,int>.
        assert 6 == KindUInt64;
        var kinds: map<Blkno, Kind> := map[513:=6];
        var jrnl := NewJrnl(kinds);

        assert forall n: nat :: n < 512 ==>
            (var acct := Acct(n);
             && acct in jrnl.domain
             && jrnl.size(acct) == 64);

        var init_acct := encode_acct(init_bal);
        var n := 0;
        while n < 512
        modifies jrnl
        invariant jrnl.Valid()
        invariant forall k:: 0 <= k < n ==> acct_val(jrnl, Acct(k), init_bal as nat)
        {
            jrnl.Write(Acct(n), init_acct);
            n := n + 1;
        }

        this.jrnl := jrnl;

        // NOTE: this was really annoying to figure out - turns out needed the
        // accounts to be a repeat of nats instead of uint64 (hence the extra
        // let binding and type annotations)
        var new_accts: seq<nat> := repeat(init_bal as nat, 512);
        sum_repeat(init_bal as nat, 512);
        accts := new_accts;
        acct_sum := 512*(init_bal as nat);
    }

    // NOTE: this should be interpreted as the body of a transaction, which
    // needs to be surrounded with code to check for errors and abort
    method transfer(acct1: nat, acct2: nat)
    requires Valid() ensures Valid()
    modifies {this,jrnl}
    requires acct1 < 512 && acct2 < 512 && acct1 != acct2
    requires 0 < accts[acct1]
    requires accts[acct2] < 0x1_0000_0000_0000_0000-1
    ensures accts == old(accts[acct1:=accts[acct1]-1][acct2:=accts[acct2]+1])
    {
        var x := jrnl.Read(Acct(acct1), 64);
        var acct1_val: uint64 := decode_acct(x, accts[acct1]);
        var x' := encode_acct(acct1_val-1);
        jrnl.Write(Acct(acct1), x');
        sum_update(accts, acct1, (acct1_val-1) as nat);
        accts := accts[acct1:=(acct1_val-1) as nat];

        x := jrnl.Read(Acct(acct2), 64);
        var acct2_val: uint64 := decode_acct(x, accts[acct2]);
        x' := encode_acct(acct2_val+1);
        jrnl.Write(Acct(acct2), x');
        sum_update(accts, acct2, (acct2_val+1) as nat);
        accts := accts[acct2:=(acct2_val+1) as nat];

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

}
