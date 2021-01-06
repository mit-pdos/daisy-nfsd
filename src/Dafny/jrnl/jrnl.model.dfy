include "jrnl.s.dfy"
include "../machine/machine.model.dfy"

module Jrnl_model refines JrnlSpec {
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

    class Jrnl {
        constructor(kinds: map<Blkno, Kind>)
        {
            var data: map<Addr, Object> :=
                map a:Addr | a in addrsForKinds(kinds)
                            :: zeroObject(kinds[a.blkno]);
            assert forall a:Addr :: a in data <==>
                && a.blkno in kinds
                && a.off < 4096*8
                && a.off % kindSize(kinds[a.blkno]) == 0;
            this.kinds := kinds;
            this.data := data;
            this.domain := map_domain(data);
        }

        method Read(a: Addr, sz: nat)
        returns (buf:Bytes)
        {
            ghost var k := kinds[a.blkno];
            kindSize_bounds(k);
            return new Bytes(data[a]);
        }

        method Write(a: Addr, bs: Bytes)
        {
            data := data[a:=bs.data];
        }
    }
}
