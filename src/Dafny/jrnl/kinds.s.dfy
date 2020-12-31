include "../util/pow.dfy"

// NOTE: we would like kinds to be represented by their size in bits directly,
// but expressing that a kind is a power of two would be complicated, so we
// define them as the power of two. This is easier to work with but annoying to
// construct.
type Kind = k:int | 0 <= k <= 15

const KindByte: Kind := 3
const KindUInt64: Kind := KindByte + 3
const KindInode: Kind := KindByte + 7 // 2^7 = 128 bytes

function method kindSize(k: Kind): (sz:nat)
ensures sz > 0
{
    pow_pos(2, k);
    pow(2,k)
}

function kindCount(k: Kind): nat
{
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
    }
}

lemma lemma_kind_at_least_byte(k: Kind)
requires k >= 3
ensures kindSize(k)/8*8 == kindSize(k)
{
    lemma_kind_at_least_byte_iff(k);
}
