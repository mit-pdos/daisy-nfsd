module Arith {
  lemma div_mod_split(x: nat, k: nat)
      requires 0 < k
      ensures x == (x/k)*k + x%k
  {}

  lemma div_mod_bound(x1: nat, x2: nat, x1_bound: nat, k:nat)
      requires 0 < k
      requires x1 < x1_bound
      requires x2 < k
      ensures x1*k + x2 < k*x1_bound
  {
      //assert x1 <= x1_bound-1;
      calc {
          x1 * k;
          <= (x1_bound-1)*k;
          == x1_bound*k-k;
      }
  }

  lemma mul_incr(x: nat, y: nat, k: nat)
    requires 0 < k
    requires x < y
    ensures x*k < y*k
  {}

  lemma div_incr(x: nat, y: nat, k: nat)
    requires 0 < k
    requires x < k * y
    ensures x / k < y
  {}

  lemma mod_bound(x: nat, k: nat)
    requires 0 < k
    ensures x%k < k
  {}
}
