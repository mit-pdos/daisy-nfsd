include "../util/marshal.i.dfy"
include "../jrnl/jrnl.s.dfy"

module Bank {

import Arith
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
    ghost var accts: seq<nat>;
    ghost const acct_sum: nat;

    var jrnl: Jrnl;

    static const BankKinds : map<Blkno, Kind> := map[513:=6]
    static lemma bank_kinds_is_correct__()
        ensures BankKinds[513] == KindUInt64
    {}

    static function method Acct(n: uint64): (a:Addr)
    requires n < 512
    ensures a.off as nat % kindSize(KindUInt64) == 0
    {
        assert kindSize(KindUInt64) == 64;
        Arith.mul_mod(n as nat, 64);
        Addr(513, n*64)
    }

    static predicate acct_val(jrnl: Jrnl, acct: uint64, val: nat)
    reads jrnl
    requires jrnl.Valid()
    requires jrnl.kinds == BankKinds
    requires acct < 512
    {
        jrnl.in_domain(Acct(acct));
        && val < U64.MAX
        && jrnl.data[Acct(acct)] == ObjData(seq_encode([EncUInt64(val as uint64)]))
    }

    // pure version of Valid for crash condition
    static predicate ValidState(jrnl: Jrnl, accts: seq<nat>, acct_sum: nat)
        reads jrnl
    {
        && jrnl.Valid()
        && jrnl.kinds == BankKinds
        && |accts| == 512
        && forall n: uint64 :: n < 512 ==>
            (var acct_ := Acct(n);
             && acct_ in jrnl.data
             && jrnl.size(acct_) == 64
             && accts[n] < U64.MAX
             && acct_val(jrnl, n, accts[n]))
        && acct_sum == sum_nat(accts)
    }

    predicate Valid()
        reads this, jrnl
    {
        && ValidState(jrnl, accts, acct_sum)
    }

    static method encode_acct(x: uint64) returns (bs:Bytes)
    ensures fresh(bs)
    ensures bs.Valid()
    ensures seq_encode([EncUInt64(x)]) == bs.data
    {
        var enc := new Encoder(8);
        enc.PutInt(x);
        enc.is_complete();
        bs := enc.Finish();
    }

    static method decode_acct(bs:Bytes, ghost x: nat) returns (x': uint64)
    requires x < U64.MAX
    requires bs.Valid()
    requires seq_encode([EncUInt64(x as uint64)]) == bs.data
    ensures x' as nat == x
    {
        var dec := new Decoder();
        dec.Init(bs, [EncUInt64(x as uint64)]);
        x' := dec.GetInt(x as uint64);
    }

    constructor Init(d: Disk, init_bal: uint64)
    ensures Valid()
    ensures forall n: nat:: n < 512 ==> accts[n] == init_bal as nat
    ensures acct_sum == 512*(init_bal as nat)
    {
        // BUG: we can't actually use the constant because then Dafny makes the type
        // of the map display expression map<int,int>.
        assert 6 == KindUInt64;
        var kinds: map<Blkno, Kind> := map[513:=6];
        var jrnl := NewJrnl(d, kinds);

        assert kindSize(jrnl.kinds[513]) == 64;
        forall n: uint64 | n < 512
            ensures Acct(n) in jrnl.data
            ensures jrnl.size(Acct(n)) == 64
        {
            ghost var acct := Acct(n);
            jrnl.in_domain(acct);
            jrnl.has_size(acct);
        }

        var txn := jrnl.Begin();
        var init_acct := encode_acct(init_bal);
        var n := 0;
        while n < 512
        modifies jrnl
        invariant txn.jrnl == jrnl
        invariant txn.Valid()
        invariant n <= 512
        invariant forall k {:trigger Acct(k)} :: 0 <= k < n ==> acct_val(jrnl, k, init_bal as nat)
        {
            txn.Write(Acct(n), init_acct);
            n := n + 1;
        }
        var _ := txn.Commit();

        this.jrnl := jrnl;

        // NOTE: this was really annoying to figure out - turns out needed the
        // accounts to be a repeat of nats instead of uint64 (hence the extra
        // let binding and type annotations)
        var new_accts: seq<nat> := repeat(init_bal as nat, 512);
        sum_repeat(init_bal as nat, 512);
        accts := new_accts;
        acct_sum := 512*(init_bal as nat);
    }

    constructor Recover(jrnl: Jrnl, ghost accts: seq<nat>, ghost acct_sum: nat)
        requires ValidState(jrnl, accts, acct_sum)
        ensures Valid()
        ensures this.jrnl == jrnl
        ensures this.accts == accts
        ensures this.acct_sum == acct_sum
    {
        this.jrnl := jrnl;
        this.accts := accts;
        this.acct_sum := acct_sum;
    }

    ghost method inc_acct(acct: uint64, amt: int)
        modifies this
        requires acct as nat < |accts|
        requires no_overflow(accts[acct], amt)
        ensures accts == old(accts[acct as nat:=accts[acct] + amt])
        ensures sum_nat(accts) == old(sum_nat(accts) + amt)
    {
        sum_update(accts, acct as nat, accts[acct] as nat + amt);
        accts := accts[acct as nat:=accts[acct] + amt];
    }

    method Transfer(acct1: uint64, acct2: uint64)
    requires Valid() ensures Valid()
    modifies this, jrnl
    requires && acct1 < 512 && acct2 < 512 && acct1 != acct2
    requires && no_overflow(accts[acct1], -1) && no_overflow(accts[acct2], 1)
    ensures accts == old(accts[acct1 as nat:=accts[acct1]-1][acct2 as nat:=accts[acct2]+1])
    {
        var txn := jrnl.Begin();
        var x := txn.Read(Acct(acct1), 64);
        var acct1_val: uint64 := decode_acct(x, accts[acct1]);
        var x' := encode_acct(acct1_val-1);
        txn.Write(Acct(acct1), x');
        inc_acct(acct1, -1);

        x := txn.Read(Acct(acct2), 64);
        var acct2_val: uint64 := decode_acct(x, accts[acct2]);
        x' := encode_acct(acct2_val+1);
        txn.Write(Acct(acct2), x');
        inc_acct(acct2, 1);
        var _ := txn.Commit();
    }

    method Get(acct: uint64)
        returns (bal: uint64)
        requires Valid() ensures Valid()
        requires acct < 512
        ensures bal as nat == accts[acct]
    {
        var txn := jrnl.Begin();
        var x := txn.Read(Acct(acct), 64);
        bal := decode_acct(x, accts[acct]);
    }

    // this is kind of silly but it gets the point across (without requiring the
    // reader to understand Valid())
    method Audit() returns (b:bool)
    modifies {}
    requires Valid()
    ensures b == (sum_nat(accts) == acct_sum)
    {
        return true;
    }
}

}
