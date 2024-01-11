include "../util/pow.dfy"

module Kinds
{

  import Pow

  // NOTE: we would like kinds to be represented by their size in bits directly,
  // but expressing that a kind is a power of two would be complicated, so we
  // define them as the power of two. This is easier to work with but annoying to
  // construct.
  type Kind = k:int | 0 == k || 3 <= k <= 15

  const KindBit: Kind := 0
  const KindByte: Kind := 3
  const KindUInt64: Kind := KindByte + 3
  const KindInode: Kind := KindByte + 7 // 2^7 = 128 bytes
  const KindBlock: Kind := 15

  // kindSize interprets a kind as a size in bits
  function kindSize(k: Kind): (sz:nat)
    ensures sz > 0
  {
    Pow.pow_pos(2, k);
    Pow.pow(2, k)
  }

}
