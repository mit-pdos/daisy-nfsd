function pow(x:int, k:nat): int decreases k {
    if k == 0 then 1 else x * pow(x,k-1)
}
lemma {:induction k1} pow_plus(x: int, k1: nat, k2: nat)
requires 1 <= x
ensures pow(x, k1) * pow(x, k2) == pow(x, k1+k2)
{
}

lemma {:induction k} pow_nonneg(x: int, k: nat)
requires 1 <= x
ensures 0 <= pow(x, k)
{
}

lemma mul_increasing(x1: nat, x2: nat)
ensures x1 <= x1 * x2
{
    // TODO: wat how do I do this
    assume false;
}

lemma {:induction k1} pow_increasing(x: int, k1: nat, k2: nat)
requires 1 <= x
ensures pow(x, k1) <= pow(x, k1+k2)
{
    pow_nonneg(x, k1);
    pow_nonneg(x, k2);
    pow_plus(x, k1, k2);
    mul_increasing(pow(x,k1), pow(x,k2));
}
