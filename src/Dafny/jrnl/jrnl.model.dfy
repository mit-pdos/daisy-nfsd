include "jrnl.s.dfy"
include "../machine/machine.model.dfy"

module Jrnl_model refines JrnlSpec {
    function method addrsForKinds(kinds: map<Blkno, Kind>): (addrs:set<Addr>)
    ensures hasDomainForKinds(kinds, addrs)
    {
        // TODO: kind of a bummer that we have to repeat the body of
        // hasDomainForKinds, but in a function method can't use the "somehow
        // assign" form :|
        set blkno : Blkno, off : int |
        && blkno in kinds
        && 0 <= off < 4096*8
        && off % kindSize(kinds[blkno]) == 0
        :: Addr(blkno, off)
    }

    class Jrnl {
        constructor(kinds: map<Blkno, Kind>)
        {
            var data: map<Addr, Object> :=
                map a:Addr | a in addrsForKinds(kinds)
                            :: zeroObject(kinds[a.blkno]);
            this.kinds := kinds;
            this.data := data;
            this.domain := map_domain(data);
        }

        method Read(a: Addr, sz: nat)
        returns (buf:Bytes)
        {
            ghost var k := kinds[a.blkno];
            kindSize_bounds(k);
            return new Bytes(data[a].bs);
        }

        method ReadBit(a: Addr) returns (b:bool)
        {
            return data[a].b;
        }

        method Write(a: Addr, bs: Bytes)
        {
            data := data[a:=ObjData(bs.data)];
        }

        method WriteBit(a: Addr, b: bool)
        {
            data := data[a:=ObjBit(b)];
        }
    }

    method NewJrnl(kinds: map<Blkno, Kind>)
    returns (jrnl:Jrnl)
    {
        return new Jrnl(kinds);
    }
}
