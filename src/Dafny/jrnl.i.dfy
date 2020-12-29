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
    ghost const domain: set<Addr>;
    const kinds: map<Blkno, Kind>;
    var has_readbuf: bool;

    predicate Valid() reads this {
        && (forall a :: a in data ==>
            && a.blkno in kinds
            && objSize(data[a]) == kindSize(kinds[a.blkno]))
        && (forall a :: a in data <==> a in domain)
    }

    constructor(kinds: map<Blkno, Kind>)
    {
        this.kinds := kinds;
        // TODO: initializing data based on kinds is quite difficult
        var data: map<Addr, Object>;
        this.data := data;
        this.domain := set a:Addr | a in data;
        new;
        assume Valid();
    }

    function size(a: Addr): nat
    requires a in this.domain
    {
        kindSize(this.kinds[a.blkno])
    }

    method Read(a: Addr, sz: nat)
    returns (buf:ReadBuf)
    requires Valid()
    modifies this
    requires !has_readbuf
    requires a in domain
    requires sz == size(a)
    ensures
    && data == old(data)
    && has_readbuf
    && buf.a == a
    && buf.obj == data[a]
    && objSize(buf.obj) == sz
    && buf.jrnl == this
    {
        has_readbuf := true;
        return new ReadBuf(a, data[a], this);
    }

    method Write(a: Addr, obj: Object)
    requires Valid() ensures Valid()
    modifies this
    requires !has_readbuf
    requires a in domain
    requires objSize(obj) == size(a)
    ensures
    && data == old(data)[a:=obj]
    && has_readbuf == old(has_readbuf)
    {
        data := data[a:=obj];
    }
}

class ReadBuf
{
    var a: Addr;
    var obj: Object;
    var jrnl: Jrnl;

    constructor(a: Addr, obj: Object, jrnl: Jrnl)
    requires jrnl.Valid()
    requires a in jrnl.domain
    requires jrnl.has_readbuf
    requires objSize(obj) == jrnl.size(a)
    ensures Valid()
    ensures
    && this.a == a
    && this.obj == obj
    && this.jrnl == jrnl;
    {
        this.a := a;
        this.obj := obj;
        this.jrnl := jrnl;
    }

    predicate Valid()
    reads this, jrnl, jrnl.Repr
    {
        && jrnl.Valid()
        && a in jrnl.domain
        && objSize(obj) == jrnl.size(a)
        && jrnl.has_readbuf
    }

    method Finish()
    modifies jrnl
    requires Valid()
    ensures !Valid() && jrnl.Valid()
    ensures jrnl.data == old(jrnl.data)
    ensures !jrnl.has_readbuf
    {
        jrnl.has_readbuf := false;
    }

    // SetDirty() models writing the buffer out after manually changing the
    // object
    method SetDirty()
    modifies jrnl;
    requires Valid()
    // intentionally does not guarantee validity (consumes the buffer)
    ensures !Valid() && jrnl.Valid()
    ensures !jrnl.has_readbuf
    {
        Finish();
        jrnl.Write(a, obj);
    }
}
