include "jrnl.s.dfy"

const acct1: Addr := Addr(513, 0);
const acct2: Addr := Addr(513, 8*8);

/*
Demo of bank transfer using axiomatized journal API
*/
class Bank
{
    var jrnl: Jrnl;
    constructor()
    ensures this.Valid()
    {
        // BUG: we can't actually use the constant because then Dafny makes the type
        // of the map display expression map<int,int>.
        assert 6 == KindUint64;
        var kinds: map<Blkno, Kind> := map[513:=6];
        this.jrnl := new Jrnl(kinds);
    }

    predicate Valid()
    reads this, jrnl, jrnl.Repr
    {
        && jrnl.Valid()
        && !jrnl.has_readbuf
        && acct1 in jrnl.domain
        && acct2 in jrnl.domain
        && jrnl.size(acct1) == 64
        && jrnl.size(acct2) == 64
    }

    // NOTE: this should be interpreted as the body of a transaction, which
    // needs to be surrounded with code to check for errors and abort
    method transfer()
    requires Valid() ensures Valid()
    modifies jrnl
    {
        var x := jrnl.Read(acct1, 64);
        x.Finish();
        jrnl.Write(acct2, x.obj);
    }
}
