include "jrnl.i.dfy"

/*
Demo of bank transfer using axiomatized journal API
*/
class Bank {
    var jrnl: Jrnl;
    constructor(jrnl: Jrnl)
    requires jrnl.Valid()
    ensures this.Valid()
    {
        this.jrnl := jrnl;
    }

    predicate Valid()
    reads {this,this.jrnl} + this.jrnl.Repr
    {
        this.jrnl.Valid()
    }

    method transfer(acct1: Addr, acct2: Addr, sz: nat)
    requires Valid()
    requires acct1 in jrnl.domain()
    requires acct2 in jrnl.domain()
    requires jrnl.size(acct1) == sz
    requires jrnl.size(acct2) == sz
    modifies {this.jrnl} + this.jrnl.Repr
    {
        assert acct1 in jrnl.domain();
        var txn := jrnl.Begin();
        var x := txn.Read(acct1, sz);
        txn.Write(acct2, x);
        txn.Commit();
    }
}
