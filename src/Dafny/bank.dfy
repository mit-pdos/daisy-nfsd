include "jrnl.i.dfy"

/*
Demo of bank transfer using axiomatized journal API
*/
class Bank
{
    var jrnl: Jrnl;
    constructor(jrnl: Jrnl)
    requires jrnl.Valid()
    ensures this.Valid()
    {
        this.jrnl := jrnl;
    }

    predicate Valid()
    reads this, jrnl, jrnl.Repr
    {
        this.jrnl.Valid()
    }

    // NOTE: this should be interpreted as the body of a transaction, which
    // needs to be surrounded with code to check for errors and abort
    method transfer(acct1: Addr, acct2: Addr, sz: nat)
    requires Valid() ensures Valid()
    requires acct1 in jrnl.domain()
    requires acct2 in jrnl.domain()
    requires jrnl.size(acct1) == sz
    requires jrnl.size(acct2) == sz
    modifies jrnl
    {
        var x := jrnl.Read(acct1, sz);
        jrnl.Write(acct2, x);
    }
}
