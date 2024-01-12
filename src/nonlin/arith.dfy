// -*- dafny-prover-local-args: ("/z3opt:smt.arith.nl=true" "/arith:1") -*-
module Arith {
  lemma div_mod_split(x: nat, k: nat)
    requires 0 < k
    ensures x == (x/k)*k + x%k
    ensures 0 <= x/k
    ensures x%k < k
  {}

  lemma mul_add_bound(x1: nat, x2: nat, x1_bound: nat, k:nat)
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

  lemma mul_r_strictly_incr(x: int, y: int, k: int)
    requires 0 < k
    requires x < y
    ensures x*k < y*k
  {}

  lemma mul_r_incr(x: int, y: int, k:int)
    requires 0 < k
    requires x <= y
    ensures x*k <= y*k
  {}

  lemma mul_comm(x: int, y: int)
    ensures x * y == y * x
  {}

  lemma mul_assoc(x: int, y: int, z: int)
    ensures x*(y*z) == (x * y) * z
  {}

  lemma mul_incr_auto()
    ensures forall x, y, k :: 0 < k && x < y ==> x*k < y*k
    ensures forall x, y, k :: 0 < k && x <= y ==> x*k <= y*k
  {}

  lemma mul_r_increasing(x1: nat, x2: nat)
    requires 0 < x2
    ensures x1 <= x1 * x2
  {}

  lemma mul_increasing(x1: nat, x2: nat, k: nat)
    requires 0 <= k
    requires x1 <= x2
    ensures x1 * k <= x2 * k
  {}

  lemma mul_positive(x: nat, y: nat)
    ensures 0 <= x*y
  {}

  lemma mod_bound(x: nat, k: nat)
    requires 0 < k
    ensures x%k < k
  {}

  lemma mul_distr_add_l(x: int, y: int, z: int)
    ensures x*(y+z) == x*y + x*z
  {}

  lemma mul_distr_add_r(x: int, y: int, z: int)
    ensures (x+y)*z == x*z + y*z
  {}

  lemma mul_distr_sub_l(x: int, y: int, z: int)
    ensures x*(y-z) == x*y - x*z
  {}

  lemma mul_distr_sub_r(x: int, y: int, z: int)
    ensures (x-y)*z == x*z - y*z
  {}

  lemma div_incr(x: nat, y: nat, k: nat)
    requires 0 < k
    requires x < k * y
    ensures x / k < y
  {}

  lemma div_incr_auto()
    ensures forall x:nat, y:nat, k:nat | 0 < k && x < k * y :: x / k < y
  {
    forall x:nat, y:nat, k:nat | 0 < k && x < k * y
      ensures x / k < y {
      div_incr(x, y, k);
    }
  }

  lemma div_positive(x: nat, y: int)
    requires 0 < y
    ensures 0 <= x / y
  {}

  lemma div_positive_auto()
    ensures forall x: nat, y: int | 0 < y :: 0 <= x / y
  {}

  // prove r is x/k by placing x in the right range
  lemma div_range(x: nat, r: nat, k: nat)
    requires 0 < k
    requires r*k <= x < (r+1)*k
    ensures x/k == r
  {
    mul_div_id(r, k);
    mul_div_id(r+1, k);
    div_increasing(r*k, x, k);
    div_incr(x, r+1, k);
  }

  lemma mod_spec(x: nat, r: nat, k: nat)
    requires 0 < k
    requires r*k <= x < (r+1)*k
    ensures x%k == x - (r*k)
  {
    div_range(x, r, k);
  }

  lemma div_mod_spec(x: nat, r: nat, k: nat)
    requires 0 < k
    requires r*k <= x < (r+1) * k
    ensures x/k == r
    ensures x%k == x - (r*k)
  {
    div_range(x, r, k);
    mod_spec(x, r, k);
  }

  // TODO: prove these basic properties of mul, mod, div

  lemma {:axiom} mod_add(a: nat, b: nat, k: nat)
    requires 0 < k
    ensures (a + b) % k == (a%k + b%k) % k

  lemma {:axiom} mul_div_id(a: nat, k: nat)
    requires 0 < k
    ensures (a*k) / k == a

  lemma div_increasing(x: nat, y: nat, k: nat)
    requires 0 < k
    requires x <= y
    ensures x / k <= y / k
  {
    div_mod_split(x, k);
    div_mod_split(y, k);
    assert (x/k - y/k) * k <= y%k - x%k;
    if x/k <= y/k { return; }
    // if x/k > y/k we'll derive a contradiction
    assert x/k - y/k >= 1;
    mul_r_incr(1, x/k - y/k, k);
    assert (x/k - y/k) * k >= k;
    assert false;
  }

  lemma round_incr(x1: nat, x2: nat, k: nat)
    requires x1 <= x2
    requires 1 <= k
    ensures x1/k*k <= x2/k*k
  {
    div_increasing(x1, x2, k);
  }


  lemma mul_mod(a: nat, k: nat)
    requires 0 < k
    ensures a * k % k == 0
  {
    div_mod_split(a*k, k);
    mul_div_id(a, k);
  }

  lemma mod_add_modulus(a: nat, k: nat)
    requires 0 < k
    ensures (a + k) % k == a % k
  {
    mod_add(a, k, k);
  }

  lemma divisible_bound(x: nat, y: nat, k: nat)
    requires 0 < k
    requires x < y
    requires x % k == 0 && y % k == 0
    ensures x + k <= y
  {
    if x/k == y/k {
      assert false;
    }
    assert x/k < y/k by {
      div_increasing(x, y, k);
    }
    assert x/k + 1 <= y/k;
    calc {
      x + k;
    ==
      (x/k + 1) * k;
    <=
      y/k*k;
    ==
      y;
    }
  }

  lemma zero_mod(k: int)
    requires k != 0
    ensures 0 % k == 0
  {}

  lemma mul_1(x: int)
    ensures x * 1 == x
  {}

  lemma mul_neg_1_r(x: int)
    ensures x * -1 == -x
  {}

  lemma mul_neg_1_l(x: int)
    ensures -1 * x == -x
  {}

  lemma plus_neg(x: int, y: int)
    ensures x + (-y) == x - y
  {}

}
