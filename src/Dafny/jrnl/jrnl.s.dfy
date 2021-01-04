include "../machine/machine.s.dfy"
include "../util/pow.dfy"
include "../util/collections.dfy"
include "kinds.s.dfy"

/*
Spec for sequential journal API, assuming we're using 2PL.
*/

type Blkno = nat
datatype Addr = Addr(blkno: Blkno, off: nat)
type Object = seq<byte>

function method objSize(obj: Object): nat
{
    |obj| * 8
}

function method zeroObject(k: Kind): (obj:Object)
requires k >= 3
ensures objSize(obj) == kindSize(k)
{
    kind_at_least_byte(k);
    repeat(0 as bv8, kindSize(k)/8)
}

function method addrsForKinds(kinds: map<Blkno, Kind>): (addrs:set<Addr>)
ensures forall a:Addr :: (&& a.blkno in kinds
                          && 0 <= a.off < 4096*8
                          && a.off % kindSize(kinds[a.blkno]) == 0) <==> a in addrs
{
    var addrs := set blkno : Blkno, off : int |
    && blkno in kinds
    && 0 <= off < 4096*8
    :: Addr(blkno, off);
    assert forall a:Addr :: a.blkno in kinds && 0 <= a.off < 4096*8 ==> a in addrs;
    // NOTE: need to create the set above and then restrict it for Dafny's
    // finite set comprehension heuristics to work
    set a:Addr |
    && a in addrs
    && (var k := kinds[a.blkno];
        a.off % kindSize(k) == 0)
}

class Jrnl
{
    var data: map<Addr, Object>;
    // we cache the domain of data to easily show that it's constant
    // NOTE: the entire Jrnl object is a spec, so having ghost state in it is
    // really strange (it's state that isn't even needed to specify the object's
    // behavior)
    ghost const domain: set<Addr>;
    const kinds: map<Blkno, Kind>;
    var has_readbuf: bool;

    predicate ValidButReading()
    reads this
    {
        && (forall a :: a in data ==>
            && a.blkno in kinds
            && objSize(data[a]) == kindSize(kinds[a.blkno]))
        && (forall a :: a in data <==> a in domain)
    }

    predicate Valid()
    reads this
    {
        && ValidButReading()
        && !has_readbuf
    }

    constructor(kinds: map<Blkno, Kind>)
    requires forall blkno | blkno in kinds :: blkno >= 513
    requires forall blkno | blkno in kinds :: kinds[blkno] >= 3
    ensures Valid()
    ensures forall a:Addr :: (&& a.blkno in kinds
                              && a.off < 4096*8
                              && (var k := kinds[a.blkno];
                                a.off % kindSize(k) == 0)) <==>
                             a in domain
    ensures this.kinds == kinds
    ensures forall a:Addr :: a in domain ==>
            data[a] == zeroObject(kinds[a.blkno])
    {
        this.kinds := kinds;
        var data: map<Addr, Object> :=
            map a:Addr | a in addrsForKinds(kinds)
                         :: zeroObject(kinds[a.blkno]);
        assert forall a:Addr :: a in data <==>
             && a.blkno in kinds
             && a.off < 4096*8
             && a.off % kindSize(kinds[a.blkno]) == 0;
        this.data := data;
        this.domain := map_domain(data);
        this.has_readbuf := false;
    }

    function size(a: Addr): nat
    reads this
    requires ValidButReading()
    requires a in domain
    {
        kindSize(this.kinds[a.blkno])
    }

    predicate has_kind(a: Addr, k: Kind)
    reads this
    requires ValidButReading()
    {
        && a in domain
        && kinds[a.blkno] == k
    }

    method Read(a: Addr, sz: nat)
    returns (buf:ReadBuf)
    requires Valid() ensures ValidButReading()
    modifies this
    requires a in domain && sz == size(a)
    ensures
    && fresh(buf)
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
    modifies this
    requires Valid() ensures Valid()
    requires a in domain && objSize(obj) == size(a)
    ensures data == old(data)[a:=obj]
    {
        data := data[a:=obj];
    }
}

class ReadBuf
{
    const a: Addr;
    var obj: Object;
    var jrnl: Jrnl;

    constructor(a: Addr, obj: Object, jrnl: Jrnl)
    requires jrnl.ValidButReading()
    requires a in jrnl.domain && objSize(obj) == jrnl.size(a)
    requires jrnl.has_readbuf
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
    reads this, jrnl
    {
        && jrnl.ValidButReading()
        && a in jrnl.domain
        && objSize(obj) == jrnl.size(a)
        && jrnl.has_readbuf
    }

    method Finish()
    modifies jrnl
    requires Valid()
    ensures !Valid() && jrnl.Valid()
    ensures jrnl.data == old(jrnl.data)
    ensures obj == old(obj)
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
    ensures jrnl.data == old(jrnl.data)[a:=obj]
    {
        Finish();
        jrnl.Write(a, obj);
    }
}
