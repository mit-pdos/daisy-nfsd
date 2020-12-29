include "pow.dfy"

/*
Spec for sequential journal API, assuming we're using 2PL.
*/

type Blkno = nat
datatype Addr = Addr(blkno: Blkno, off: nat)
type byte = bv8
type Object = array<byte>
type Kind = k:int | 0 <= k <= 15

function objSize(obj: Object): nat
{
    obj.Length * 8
}

function kindSize(k: Kind): nat
{
    pow_nonneg(2, k);
    pow(2,k)
}

function kindCount(k: Kind): nat
{
    pow_nonneg(2, 15-k);
    pow(2, 15-k)
}

lemma kindSize_and_kindCount_sensible(k: Kind)
ensures kindSize(k) * kindCount(k) == 4096*8
{
    assert 4096*8 == pow(2, 15);
    pow_plus(2, k, 15-k);
}

lemma kindSize_bounds(k: Kind)
ensures kindSize(k) <= 4096*8
{
    pow_increasing(2, k, 15);
    assert pow(2,15) == 4096*8;
}

class {:autocontracts} Jrnl
{
    var data: map<Addr, Object>;
    var kinds: map<Blkno, Kind>;

    predicate Valid() reads this {
        forall a :: a in data ==>
        && a.blkno in kinds
        && objSize(data[a]) == kindSize(kinds[a.blkno])
    }

    constructor(kinds: map<Blkno, Kind>)
    {
        this.kinds := kinds;
        // TODO: initializing data based on kinds is quite difficult
        new;
        assume Valid();
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

    method Read(a: Addr, sz: nat)
    returns (obj:Object)
    requires Valid()
    modifies {}
    requires a in domain()
    requires sz == size(a)
    ensures objSize(obj) == sz
    {
        return data[a];
    }

    method Write(a: Addr, obj: Object)
    requires Valid() ensures Valid()
    modifies this
    requires a in domain()
    requires objSize(obj) == size(a)
    //ensures jrnl.data == old(jrnl.data)[a:=obj]
    ensures kinds == old(kinds)
    {
        data := data[a:=obj];
    }
}
