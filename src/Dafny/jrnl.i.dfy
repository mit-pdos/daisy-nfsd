include "pow.dfy"

datatype Addr = Addr(blkno: nat, off: nat)
type byte = bv8
type Object = array<byte>
type Kind = k:int | 0 <= k <= 15
function kindSize(k: Kind): int {
    pow(2,k)
}

lemma kindSize_bounds(k: Kind)
ensures kindSize(k) <= 4096*8 {
    pow_increasing(2, k, 15);
    assert pow(2,15) == 4096*8;
}

class Jrnl {
    ghost var data: map<Addr, Object>;
    ghost var kinds: map<nat, Kind>;

    predicate Valid() reads this {
        forall a :: a in data ==>
        && a.blkno in kinds
        && data[a].Length == kindSize(kinds[a.blkno])
    }
}