/*
Uninteresting definition of pow (exponentiation)
*/

function method pow(x:nat, k:nat): (p:nat) decreases k
ensures 1 <= x ==> 1 <= p
{
    if k == 0 then 1 else x * pow(x,k-1)
}
lemma {:induction k1} pow_plus(x: nat, k1: nat, k2: nat)
ensures pow(x, k1) * pow(x, k2) == pow(x, k1+k2)
{
}

lemma {:induction k} pow_pos(x: nat, k: nat)
requires 0 < x
ensures 0 < pow(x, k)
{
}

// TODO: don't know how to prove this
lemma {:axiom} mul_increasing(x1: nat, x2: nat)
ensures x1 <= x1 * x2

lemma {:induction k1} pow_increasing(x: nat, k1: nat, k2: nat)
ensures pow(x, k1) <= pow(x, k1+k2)
{
    pow_plus(x, k1, k2);
    mul_increasing(pow(x,k1), pow(x,k2));
}
