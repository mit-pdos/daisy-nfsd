include "../machine/machine.s.dfy"
include "../util/pow.dfy"
include "../util/collections.dfy"
include "kinds.s.dfy"

/*
Spec for sequential journal API, assuming we're using 2PL.
*/

module JrnlSpec
{

import opened Machine
import opened Kinds
import opened bytes
import opened Collections

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

    predicate Valid()
    reads this
    {
        && (forall a :: a in data ==>
            && a.blkno in kinds
            && objSize(data[a]) == kindSize(kinds[a.blkno]))
        && (forall a :: a in data <==> a in domain)
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
    }

    function size(a: Addr): nat
    reads this
    requires Valid()
    requires a in domain
    {
        kindSize(this.kinds[a.blkno])
    }

    predicate has_kind(a: Addr, k: Kind)
    reads this
    requires Valid()
    {
        && a in domain
        && kinds[a.blkno] == k
    }

    method Read(a: Addr, sz: nat)
    returns (buf:Bytes)
    requires Valid() ensures Valid()
    requires a in domain && sz == size(a)
    ensures
    && fresh(buf)
    && buf.Valid()
    && buf.data == data[a]
    && objSize(buf.data) == sz
    {
        ghost var k := kinds[a.blkno];
        kindSize_bounds(k);
        return new Bytes(data[a]);
    }

    method Write(a: Addr, bs: Bytes)
    modifies this
    requires Valid() ensures Valid()
    requires bs.Valid()
    requires a in domain && objSize(bs.data) == size(a)
    ensures data == old(data)[a:=bs.data]
    {
        data := data[a:=bs.data];
    }
}

}
