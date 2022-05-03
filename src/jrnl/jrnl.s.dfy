include "../machine/bytes.s.dfy"
include "../util/pow.dfy"
include "../util/collections.dfy"
include "kinds.s.dfy"
include "kinds_facts.dfy"

module JrnlTypes
{
    import opened Machine
    import C = Collections
    type Blkno = uint64

    type Block = b:seq<byte> | |b| == 4096 witness C.repeat(0 as byte, 4096)
    predicate is_block(b: seq<byte>) { |b| == 4096 }
    const block0: Block := C.repeat(0 as byte, 4096)
}

/*
Spec for sequential journal API, assuming we're using 2PL.
*/

module {:extern "jrnl", "github.com/mit-pdos/daisy-nfsd/dafny_go/jrnl"} JrnlSpec
{

    import opened JrnlTypes
    import opened Machine
    import opened Kinds
    import opened KindsFacts
    import opened ByteSlice
    import C = Collections

    class {:extern} Disk{}

    method DiskSize(d: Disk) returns (x: uint64)
    {}

    datatype {:extern} Addr = Addr(blkno: Blkno, off: uint64)

    datatype Object =
        | ObjData (bs:seq<byte>)
        | ObjBit (b:bool)

    function method objSize(obj: Object): nat
    {
        match obj
        case ObjData(bs) => |bs| * 8
        case ObjBit(b) => 1
    }

    function method zeroObject(k: Kind): (obj:Object)
    ensures objSize(obj) == kindSize(k)
    {
        if k == 0 then ObjBit(false)
        else
            kind_at_least_byte(k);
            ObjData(C.repeat(0 as byte, kindSize(k)/8))
    }

    predicate kindsValid(kinds: map<Blkno, Kind>)
    {
        forall a | a in kinds :: 513 <= a
    }

    // specifies the set of addresses used for a kind schema
    function method {:opaque} addrsForKinds(kinds: map<Blkno, Kind>): (addrs:set<Addr>)
    {
        set blkno : Blkno, off : uint64 |
        && blkno in kinds
        && 0 <= off < 4096*8
        && off as nat % kindSize(kinds[blkno]) == 0
        :: Addr(blkno, off)
    }

    // This is an allocator that makes no real guarantees due to being
    // stateless, so that no issues of concurrency arise.
    class {:extern} Allocator
    {
        ghost const max: uint64

        predicate Valid()
        {
            && 0 < max
            && max % 8 == 0
        }

        constructor {:extern}(max: uint64)
            requires 0 < max
            requires max%8 == 0
            ensures this.max == max
            ensures Valid()
        {
            this.max := max;
        }

        // MarkUsed prevents an index from being allocated. Used during recovery.
        method {:extern} MarkUsed(x: uint64)
            requires Valid()
            requires x < max
        {
        }

        method {:extern} Alloc() returns (x:uint64)
            requires Valid()
            ensures x < max
        {
            x := 1;
        }

        method {:extern} Free(x: uint64)
            requires Valid()
            requires x != 0
            requires x < max
        {
        }

        method {:extern} NumFree() returns (num: uint64)
            requires Valid()
            ensures num <= max
        {
            num := 0;
        }

    }

    method {:extern} NewAllocator(max: uint64) returns (a:Allocator)
        requires 0 < max
        requires max%8 == 0
        ensures a.max == max
        ensures fresh(a)
    {
        return new Allocator(max);
    }

    type JrnlData = map<Addr, Object>

    class {:extern} Jrnl
    {
        var data: JrnlData;
        ghost const kinds: map<Blkno, Kind>;

        predicate {:opaque} Valid()
        reads this
        {
            && kindsValid(kinds)
            && (forall a :: a in data ==>
                && a.blkno in kinds
                && objSize(data[a]) == kindSize(kinds[a.blkno]))
            && (forall a :: a in addrsForKinds(kinds) <==> a in data)
        }

        lemma in_domain(a: Addr)
            requires Valid()
            requires a.blkno in kinds
            requires a.off as nat % kindSize(kinds[a.blkno]) == 0
            requires a.off < 8*4096
            ensures a in data
        {
            reveal_Valid();
            reveal_addrsForKinds();
        }

        lemma has_size(a: Addr)
            requires Valid()
            requires a in data
            ensures (reveal_Valid(); objSize(this.data[a]) == this.size(a))
        {
            reveal_Valid();
        }

        constructor(kinds: map<Blkno, Kind>)
        requires kindsValid(kinds)
        ensures Valid()
        ensures this.kinds == kinds
        ensures (reveal_Valid(); forall a:Addr :: a in data ==>
                && data[a] == zeroObject(kinds[a.blkno]))
        {
            reveal_addrsForKinds();
            var data: map<Addr, Object> :=
                map a:Addr | a in addrsForKinds(kinds)
                            :: zeroObject(kinds[a.blkno]);
            this.kinds := kinds;
            this.data := data;
            new;
            reveal_Valid();
        }


        function size(a: Addr): nat
        reads this
        requires Valid()
        requires a in data
        {
            reveal_Valid();
            kindSize(this.kinds[a.blkno])
        }

        predicate has_kind(a: Addr, k: Kind)
        reads this
        requires Valid()
        {
            reveal_Valid();
            && a in data
            && kinds[a.blkno] == k
        }

        method Begin()
            returns (txn:Txn)
            // TODO: should invalidate Jrnl while a transaction is in progress
            // but lazy
            requires Valid() ensures Valid()
            ensures fresh(txn)
            ensures txn.jrnl == this
            ensures txn.Valid()
        {
            return new Txn(this);
        }
    }

    predicate same_jrnl(jrnl1: Jrnl, jrnl2: Jrnl)
        reads jrnl1, jrnl2
    {
        && jrnl1.data == jrnl2.data
        && jrnl1.kinds == jrnl2.kinds
    }

    lemma same_jrnl_valid()
        ensures forall jrnl1: Jrnl, jrnl2: Jrnl | jrnl2.Valid() && same_jrnl(jrnl1, jrnl2) ::
        jrnl1.Valid()
    {
        forall jrnl1: Jrnl, jrnl2: Jrnl | jrnl2.Valid() && same_jrnl(jrnl1, jrnl2)
            ensures jrnl1.Valid()
        {
            reveal jrnl1.Valid();
        }
    }

    class {:extern} Txn
    {

        const jrnl: Jrnl;

        constructor(jrnl: Jrnl)
            requires jrnl.Valid()
            ensures this.jrnl == jrnl
            ensures Valid()
        {
            this.jrnl := jrnl;
        }

        predicate Valid()
            reads this, jrnl
        {
            && jrnl.Valid()
        }

        method {:extern} Read(a: Addr, sz: uint64)
        returns (buf:Bytes)
        requires Valid() ensures Valid()
        requires a in jrnl.data && jrnl.size(a) == sz as nat
        // Read only works for at least byte-sized objects
        requires sz >= 8
        ensures
        && fresh(buf)
        && buf.Valid()
        && buf.data == jrnl.data[a].bs
        && objSize(jrnl.data[a]) == sz as nat
        {
            ghost var k := jrnl.kinds[a.blkno];
            kindSize_bounds(k);
            return new Bytes(jrnl.data[a].bs);
        }

        method {:extern} ReadBit(a: Addr)
        returns (b:bool)
        requires Valid() ensures Valid()
        requires a in jrnl.data && jrnl.size(a) == 1
        ensures && jrnl.data[a] == ObjBit(b)
        {
            return jrnl.data[a].b;
        }

        method {:extern} Write(a: Addr, bs: Bytes)
        modifies jrnl, bs
        requires Valid() ensures Valid()
        ensures bs.data == []
        requires bs.Valid()
        requires a in jrnl.data && jrnl.size(a) == objSize(ObjData(bs.data))
        requires 8 <= |bs.data|
        ensures jrnl.data == old(jrnl.data[a:=ObjData(bs.data)])
        {
            jrnl.data := jrnl.data[a:=ObjData(bs.data)];
            bs.data := [];
        }

        method {:extern} WriteBit(a: Addr, b: bool)
        modifies jrnl
        requires Valid() ensures Valid()
        requires a in jrnl.data && jrnl.size(a) == 1
        ensures jrnl.data == old(jrnl.data[a:=ObjBit(b)])
        {
            jrnl.data := jrnl.data[a:=ObjBit(b)];
        }

        // wait=false is not modeled; it is up to the code to use this only when
        // deferred durability is acceptable
        method {:extern} Commit(wait: bool) returns (ok:bool)
        requires wait
        requires Valid() ensures Valid()
        {
            ok := true;
        }

        method {:extern} Abort()
            requires Valid()
        {}

        method {:extern} NDirty()
            returns (num: uint64)
            requires Valid()
        {
            num := 0;
        }
    }

    // NOTE: we can't provide a model for this because we need kinds to be ghost
    // for the spec but the model uses kinds to construct the initial data
    //
    // The best we can do is manually check that NewJrnl has about the same spec
    // as the constructor, except for adding fresh(jrnl) which is implied by the
    // constructor.
    method {:extern} NewJrnl(d: Disk, ghost kinds: map<Blkno, Kind>)
    returns (jrnl:Jrnl)
    requires kindsValid(kinds)
    ensures fresh(jrnl)
    ensures jrnl.Valid()
    ensures jrnl.kinds == kinds
    ensures (jrnl.reveal_Valid(); forall a:Addr :: a in jrnl.data ==>
            && jrnl.data[a] == zeroObject(jrnl.kinds[a.blkno]))

}
