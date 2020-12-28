include "pow.dfy"

datatype Addr = Addr(blkno: nat, off: nat)
type byte = bv8
type Object = array<byte>
type Kind = k:int | 0 <= k <= 15

function kindSize(k: Kind): nat {
    pow_nonneg(2, k);
    pow(2,k)
}

function kindCount(k: Kind): nat {
    pow_nonneg(2, 15-k);
    pow(2, 15-k)
}

lemma kindSize_and_kindCount_sensible(k: Kind)
ensures kindSize(k) * kindCount(k) == 4096*8 {
    assert 4096*8 == pow(2, 15);
    pow_plus(2, k, 15-k);
}

lemma kindSize_bounds(k: Kind)
ensures kindSize(k) <= 4096*8 {
    pow_increasing(2, k, 15);
    assert pow(2,15) == 4096*8;
}

class {:autocontracts} Jrnl {
    var data: map<Addr, Object>;
    var kinds: map<nat, Kind>;

    predicate Valid() reads this {
        forall a :: a in data ==>
        && a.blkno in kinds
        && data[a].Length*8 == kindSize(kinds[a.blkno])
    }

    constructor(kinds: map<nat, Kind>)
    {
        this.kinds := kinds;
        // TODO: initializing data based on kinds is quite difficult
        assume false;
    }

    function domain(): set<Addr>
    {
        set a:Addr | a in this.data
    }

    function size(a: Addr): nat
    requires a in this.domain()
    {
        kindSize(this.kinds[a.blkno])
    }

    method Begin() returns (txn:Txn)
    {
        return new Txn(this);
    }
}

class Txn {
    var jrnl: Jrnl;

    constructor(jrnl: Jrnl)
    requires jrnl.Valid()
    {
        this.jrnl := jrnl;
    }

    predicate Valid() reads {this,this.jrnl} + this.jrnl.Repr {
        this.jrnl.Valid()
    }

    method Read(a: Addr, sz: nat)
    returns (o:Object)
    requires this.Valid()
    requires a in this.jrnl.domain()
    requires sz == this.jrnl.size(a)
    {
        return this.jrnl.data[a];
    }

    method Write(a: Addr, obj: Object)
    modifies this.jrnl
    requires this.Valid()
    requires a in this.jrnl.domain()
    requires obj.Length*8 == this.jrnl.size(a)
    {
        this.jrnl.data := this.jrnl.data[a:=obj];
    }
}
