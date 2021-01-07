include "jrnl.s.dfy"
include "../machine/machine.model.dfy"

module Jrnl_model refines JrnlSpec {
    function method addrsForKinds(kinds: map<Blkno, Kind>): (addrs:set<Addr>)
    ensures hasDomainForKinds(kinds, addrs)
    {
        // TODO: kind of a bummer that we have to repeat the body of
        // hasDomainForKinds, but in a function method can't use the "somehow
        // assign" form :|
        set blkno : Blkno, off : uint64 |
        && blkno in kinds
        && 0 <= off < 4096*8
        && off as nat % kindSize(kinds[blkno]) == 0
        :: Addr(blkno, off)
    }

    class Allocator {
        constructor(max: uint64)
        {
            this.max := max;
        }

        method Alloc()
            returns (x:uint64)
        {
            return 0;
        }

        method MarkUsed(x: uint64)
        {
        }

        method Free(x: uint64)
        {
        }
    }

    method NewAllocator(max: uint64)
        returns (a:Allocator)
    {
        a := new Allocator(max);
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
    }

    class Txn {

        method Read(a: Addr, sz: uint64)
        returns (buf:Bytes)
        {
            ghost var k := jrnl.kinds[a.blkno];
            kindSize_bounds(k);
            return new Bytes(jrnl.data[a].bs);
        }

        method ReadBit(a: Addr) returns (b:bool)
        {
            return jrnl.data[a].b;
        }

        method Write(a: Addr, bs: Bytes)
        {
            jrnl.data := jrnl.data[a:=ObjData(bs.data)];
        }

        method WriteBit(a: Addr, b: bool)
        {
            jrnl.data := jrnl.data[a:=ObjBit(b)];
        }

        method Commit()
        {
        }
    }

    // NOTE: NewJrnl is not refined because it makes kinds ghost, which matches
    // how the code works but isn't possible to do in a ghost context in Dafny
}
