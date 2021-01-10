include "../machine/machine.s.dfy"
include "../util/pow.dfy"
include "../util/collections.dfy"
include "kinds.s.dfy"

/*
Spec for sequential journal API, assuming we're using 2PL.
*/

module {:extern "jrnl", "github.com/mit-pdos/dafny-jrnl/src/dafny_go/jrnl"} JrnlSpec
{

    import opened Machine
    import opened Kinds
    import opened ByteSlice
    import opened Collections

    class {:extern} Disk{}

    type Blkno = uint64
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
            ObjData(repeat(0 as bv8, kindSize(k)/8))
    }

    predicate kindsValid(kinds: map<Blkno, Kind>)
    {
        forall a | a in kinds :: 513 <= a
    }

    // specifies that the set of addresses is the correct set for a particular
    // kind schema
    predicate hasDomainForKinds(kinds: map<Blkno, Kind>, addrs: set<Addr>)
    {
        forall a:Addr ::
          (&& a.blkno in kinds
           && a.off < 4096*8
           && a.off as nat % kindSize(kinds[a.blkno]) == 0) <==>
           a in addrs
    }

    // This is an allocator that makes no real guarantees due to being
    // stateless, so that no issues of concurrency arise.
    class {:extern} Allocator
    {
        const max: uint64;

        predicate {:opaque} Valid()
            reads this
        {
            0 < max
        }

        constructor {:extern}(max: uint64)
            requires 0 < max
            requires max%8 == 0
            ensures this.max == max
            ensures Valid()

        // MarkUsed prevents an index from being allocated. Used during recovery.
        method {:extern} MarkUsed(x: uint64)
            requires Valid() ensures Valid()
            modifies this

        method {:extern} Alloc()
            returns (x:uint64)
            requires Valid() ensures Valid()
            modifies this
            ensures x < max

        method {:extern} Free(x: uint64)
            requires Valid() ensures Valid()
            requires x <= max
            modifies this
    }

    method {:extern} NewAllocator(max: uint64)
        returns (a:Allocator)
        requires 0 < max
        requires max%8 == 0
        ensures fresh(a)
        ensures a.max == max
        ensures a.Valid()

    class {:extern} Jrnl
    {
        var data: map<Addr, Object>;
        // we cache the domain of data to easily show that it's constant
        // NOTE: the entire Jrnl object is a spec, so having ghost state in it is
        // really strange (it's state that isn't even needed to specify the object's
        // behavior)
        ghost const domain: set<Addr>;
        ghost const kinds: map<Blkno, Kind>;

        predicate Valid()
        reads this
        {
            && kindsValid(kinds)
            && (forall a :: a in data ==>
                && a.blkno in kinds
                && objSize(data[a]) == kindSize(kinds[a.blkno]))
            && (forall a :: a in data <==> a in domain)
            && hasDomainForKinds(kinds, domain)
        }

        constructor(kinds: map<Blkno, Kind>)
        requires kindsValid(kinds)
        ensures Valid()
        ensures this.kinds == kinds
        ensures forall a:Addr :: a in domain ==>
                && data[a] == zeroObject(kinds[a.blkno])


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

    class {:extern} Txn
    {

        var jrnl: Jrnl;

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
        requires a in jrnl.domain && jrnl.size(a) == sz as nat
        // Read only works for at least byte-sized objects
        requires sz >= 8
        ensures
        && fresh(buf)
        && buf.Valid()
        && buf.data == jrnl.data[a].bs
        && objSize(jrnl.data[a]) == sz as nat

        method {:extern} ReadBit(a: Addr)
        returns (b:bool)
        requires Valid() ensures Valid()
        requires a in jrnl.domain && jrnl.size(a) == 1
        ensures && jrnl.data[a] == ObjBit(b)

        method {:extern} Write(a: Addr, bs: Bytes)
        modifies jrnl
        requires Valid() ensures Valid()
        requires bs.Valid()
        requires a in jrnl.domain && jrnl.size(a) == objSize(ObjData(bs.data))
        requires 8 <= |bs.data|
        ensures jrnl.data == old(jrnl.data[a:=ObjData(bs.data)])

        method {:extern} WriteBit(a: Addr, b: bool)
        modifies jrnl
        requires Valid() ensures Valid()
        requires a in jrnl.domain && jrnl.size(a) == 1
        ensures jrnl.data == old(jrnl.data[a:=ObjBit(b)])

        method {:extern} Commit() returns (ok:bool)
        requires Valid() ensures Valid()
    }

    method {:extern} NewJrnl(d: Disk, ghost kinds: map<Blkno, Kind>)
    returns (jrnl:Jrnl)
    requires kindsValid(kinds)
    ensures fresh(jrnl)
    ensures jrnl.Valid()
    ensures jrnl.kinds == kinds
    ensures forall a:Addr :: a in jrnl.domain ==>
            && jrnl.data[a] == zeroObject(jrnl.kinds[a.blkno])

}
