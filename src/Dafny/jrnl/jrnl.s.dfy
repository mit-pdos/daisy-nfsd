include "../machine/machine.s.dfy"
include "../util/pow.dfy"

/*
Spec for sequential journal API, assuming we're using 2PL.
*/

type Blkno = nat
datatype Addr = Addr(blkno: Blkno, off: nat)
type Object = seq<byte>

// NOTE: we would like kinds to be represented by their size in bits directly,
// but expressing that a kind is a power of two would be complicated, so we
// define them as the power of two. This is easier to work with but annoying to
// construct.
type Kind = k:int | 0 <= k <= 15

const KindByte: Kind := 3
const KindUInt64: Kind := KindByte + 3
const KindInode: Kind := KindByte + 7 // 2^7 = 128 bytes

function method objSize(obj: Object): nat
{
    |obj| * 8
}

function method kindSize(k: Kind): (sz:nat)
ensures sz > 0
{
    pow_nonneg(2, k);
    pow_pos(2, k);
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

lemma lemma_kind_at_least_byte_iff(k: Kind)
ensures kindSize(k)/8*8 == kindSize(k) <==> k >= 3
{
    if k >= 3 {
        pow_plus(2, k-3, 3);
    } else {
        if k == 0 {
        } else if k == 1 {
        } else if k == 2 {
        }
    }
}

lemma lemma_kind_at_least_byte(k: Kind)
requires k >= 3
ensures kindSize(k)/8*8 == kindSize(k)
{
    lemma_kind_at_least_byte_iff(k);
}

function method
repeat<T>(x: T, count: nat): (xs:seq<T>) decreases count
ensures |xs| == count && forall i :: 0 <= i < |xs| ==> xs[i] == x
{
    if count == 0 then [] else [x] + repeat(x, count-1)
}

function method map_domain<K, V>(m: map<K, V>): set<K> {
    set k:K | k in m
}

function method zeroObject(k: Kind): (obj:Object)
requires k >= 3
ensures objSize(obj) == kindSize(k)
{
    lemma_kind_at_least_byte(k);
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

class {:autocontracts} Jrnl
{
    var data: map<Addr, Object>;
    // we cache the domain of data to easily show that it's constant
    // NOTE: the entire Jrnl object is a spec, so having ghost state in it is
    // really strange (it's state that isn't even needed to specify the object's
    // behavior)
    ghost const domain: set<Addr>;
    const kinds: map<Blkno, Kind>;
    var has_readbuf: bool;

    // NOTE: this needs autocontracts false because it otherwise has requires
    // Valid(), which is recursive
    predicate {:autocontracts false} ValidButReading()
    reads this
    {
        && this in Repr && null !in Repr
        && (forall a :: a in data ==>
            && a.blkno in kinds
            && objSize(data[a]) == kindSize(kinds[a.blkno]))
        && (forall a :: a in data <==> a in domain)
    }

    predicate Valid()
    {
        && ValidButReading()
        && !has_readbuf
    }

    constructor(kinds: map<Blkno, Kind>)
    requires forall blkno | blkno in kinds :: blkno >= 513
    requires forall blkno | blkno in kinds :: kinds[blkno] >= 3
    ensures forall a:Addr :: (&& a.blkno in kinds
                              && a.off < 4096*8
                              && (var k := kinds[a.blkno];
                                a.off % kindSize(k) == 0)) <==>
                             a in domain
    ensures this.kinds == kinds;
    // something about zero initial data?
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

    function {:autocontracts false} size(a: Addr): nat
    reads this
    requires ValidButReading()
    requires a in domain
    {
        kindSize(this.kinds[a.blkno])
    }

    predicate {:autocontracts false} has_kind(a: Addr, k: Kind)
    reads this
    requires ValidButReading()
    {
        && a in domain
        && kinds[a.blkno] == k
    }

    method {:autocontracts false} Read(a: Addr, sz: nat)
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
    requires Valid() ensures Valid()
    modifies this
    requires a in domain && objSize(obj) == size(a)
    ensures
    && data == old(data)[a:=obj]
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
    reads this, jrnl, jrnl.Repr
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
