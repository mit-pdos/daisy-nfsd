include "../../machine/machine.s.dfy"
include "../../util/arith.dfy"

module Round {
  import opened Machine
  import opened Arith

  function div_roundup(x: nat, k: nat): nat
    requires k >= 1
  {
    (x + (k-1)) / k
  }

  // TODO: prove these basic properties of mul, mod, div

  lemma {:axiom} mod_add(a: nat, b: nat, k: nat)
    requires 0 < k
    ensures (a + b) % k == (a%k + b%k) % k

  lemma {:axiom} mul_div_id(a: nat, k: nat)
    requires 0 < k
    ensures (a*k) / k == a

  lemma mul_mod(a: nat, k: nat)
    requires 0 < k
    ensures a * k % k == 0
  {
    div_mod_split(a*k, k);
    mul_div_id(a, k);
  }

  lemma mul_add_mod(a: nat, b: nat, c: nat)
    requires 0 < b
    ensures (a*b + c) % b == c % b
  {
    calc {
      (a*b + c) % b;
      { mod_add(a*b, c, b); }
      (a*b%b + c%b) % b;
      { mul_mod(a, b); }
      (c%b) % b;
      c%b;
    }
  }

  lemma div_add_l(a:nat, b:nat, c: nat)
    requires 0 < b
    ensures (a * b + c) / b == a + c / b
  {
    div_mod_split(a * b + c, b);
    mul_add_mod(a, b, c);
    assert (a*b + c) / b * b + (a*b + c) % b == (a*b + c/b*b) + (a*b + c) % b;
    assert (a*b + c) / b * b == a*b + c/b*b;
    assert (a*b + c) / b * b == (a + c/b) * b;
  }

  lemma div_small(a: nat, b:nat)
    requires a < b
    ensures a / b == 0
  {}

  lemma div_roundup_spec(x: nat, k: nat)
    requires k >= 1
    ensures div_roundup(x, k) == if x % k == 0 then x/k else x/k + 1
  {
    if x % k == 0 {
      assert x == (x/k)*k;
      assert x + (k-1) == x/k*k + (k-1);
      calc {
        (x + (k-1)) / k;
        (x/k*k + (k-1)) / k;
      { div_add_l(x/k, k, (k-1)); }
        x/k + (k-1) / k;
      { div_small(k-1, k); }
        x/k;
      }
    } else {
      calc {
        div_roundup(x, k);
        (x/k*k + x%k + (k-1)) / k;
        (x/k*k + k + (x%k-1)) / k;
        ((x/k+1)*k + (x%k-1)) / k;
        { div_add_l(x/k+1, k, (x%k-1)); }
        x/k+1 + (x%k-1)/k;
        { div_small( (x%k-1)/k, k ); }
        x/k + 1;
      }
    }
  }

  lemma div_roundup_inc(x: nat, k: nat)
    requires k >= 1
    requires x % k != 0
    ensures div_roundup(x, k) == x/k + 1
  {
    div_roundup_spec(x, k);
  }

  function method div_roundup64(x: uint64, k: uint64): (r:uint64)
    requires k >= 1
    requires x as nat < 0x1_0000_0000_0000_0000-k as nat
    ensures div_roundup(x as nat, k as nat) == r as nat
  {
    (x + (k-1)) / k
  }

  function roundup(x: nat, k: nat): nat
    requires k >= 1
  {
    div_roundup(x, k) * k
  }

  function method roundup64(x: uint64, k: uint64): (r:uint64)
    requires k >= 1
    requires x as nat < 0x1_0000_0000_0000_0000-k as nat
    ensures roundup(x as nat, k as nat) == r as nat
  {
    div_roundup64(x, k) * k
  }

  lemma div_roundup_bound(x: nat, k: nat)
    requires k >= 1
    ensures div_roundup(x, k) >= x/k
  {}

  lemma roundup_bound(x: nat, k: nat)
    requires k >= 1
    ensures roundup(x, k) >= x
  {}

  lemma roundup_distance(x: nat, k: nat)
    requires k >= 1
    ensures 0 <= roundup(x, k) - x < k
  {}
}
