/*
Uninteresting definition of pow (exponentiation)
*/

include "../nonlin/arith.dfy"

module Pow {

  import opened Arith

  function pow(x:nat, k:nat): (p:nat)
    decreases k
  {
    if k == 0 then 1 else (
      mul_positive(x, pow(x,k-1));
      x * pow(x,k-1)
    )
  }

  lemma {:induction k1} pow_plus(x: nat, k1: nat, k2: nat)
    decreases k1
    ensures pow(x, k1) * pow(x, k2) == pow(x, k1+k2)
  {
    if k1 == 0 {
      calc {
        pow(x, k1) * pow(x, k2);
        1 * pow(x, k2);
        pow(x, k2);
        pow(x, k1+k2);
      }
    } else {
      calc {
        pow(x, k1) * pow(x, k2);
        x * pow(x,k1-1) * pow(x, k2);
        { pow_plus(x, k1-1, k2); }
        { mul_assoc(x, pow(x,k1-1), pow(x, k2)); }
        x * pow(x, (k1-1) + k2);
        pow(x, k1+k2);
      }
    }
  }

  lemma {:induction k} pow_pos(x: nat, k: nat)
    decreases k
    requires 0 < x
    ensures 0 < pow(x, k)
  {
    if k == 0 {
    } else {
      pow_pos(x, k-1);
      mul_r_increasing(pow(x, k-1), x);
    }
  }

  lemma {:induction false} pow_increasing(x: nat, k1: nat, k2: nat)
    requires 0 < x
    ensures pow(x, k1) <= pow(x, k1+k2)
  {
    pow_plus(x, k1, k2);
    pow_pos(x, k2);
    mul_r_increasing(pow(x, k1), pow(x, k2));
  }

  lemma pow_incr(x: nat, k1: nat, k2: nat)
    requires 0 < x
    requires k1 <= k2
    ensures pow(x, k1) <= pow(x, k2)
  {
    pow_increasing(x, k1, k2-k1);
  }

}
