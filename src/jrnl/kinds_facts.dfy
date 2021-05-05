include "kinds.s.dfy"

module KindsFacts {

import opened Kinds
import opened Pow

lemma kind_uint64_size()
    ensures kindSize(KindUInt64) == 64
{
    assert KindUInt64 == 6;
}

lemma kind_inode_size()
    ensures kindSize(KindInode) == 128*8
{
    assert KindInode == 10;
}

lemma kind_block_size()
    ensures kindSize(KindBlock) == 4096*8
{}

lemma kindSize_bounds(k: Kind)
ensures kindSize(k) <= 4096*8
{
    pow_increasing(2, k, 15);
    assert pow(2,15) == 4096*8;
}

lemma kind_at_least_byte_iff(k: Kind)
ensures kindSize(k)/8*8 == kindSize(k) <==> k >= 3
{
    if k >= 3 {
        pow_plus(2, k-3, 3);
        assert pow(2, 3) == 8;
        assert kindSize(k)/8*8 == 8 * pow(2, k-3) / 8 * 8;
    }
}

lemma kind_at_least_byte(k: Kind)
requires k >= 3
ensures kindSize(k)/8*8 == kindSize(k)
{
    kind_at_least_byte_iff(k);
}

}
