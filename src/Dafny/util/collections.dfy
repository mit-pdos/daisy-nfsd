include "arith.dfy"

module Collections
{
import opened Arith

// fmap over sequences

function method
seq_fmap<T,U>(f: T -> U, xs: seq<T>): (ys:seq<U>) decreases xs
ensures |ys| == |xs| && forall i :: 0 <= i < |xs| ==> ys[i] == f(xs[i])
{
    if xs == [] then [] else [f(xs[0])] + seq_fmap(f, xs[1..])
}

// repeat

function method {:opaque} repeat<T>(x: T, count: nat): (xs:seq<T>)
    decreases count
    ensures |xs| == count && forall i :: 0 <= i < |xs| ==> xs[i] == x
{
    if count == 0 then [] else [x] + repeat(x, count-1)
}

lemma repeat_split<T>(x: T, count: nat, count1: nat, count2: nat)
    requires count == count1 + count2
    ensures repeat(x, count) == repeat(x, count1) + repeat(x, count2)
{}

// concat

function method concat<T>(xs: seq<seq<T>>): (ys: seq<T>)
    decreases xs
{
    if xs == [] then []
    else xs[0] + concat(xs[1..])
}

lemma {:induction ls} concat_homogeneous_len<T>(ls: seq<seq<T>>, len: nat)
    requires forall l | l in ls :: |l| == len
    ensures |concat(ls)| == len * |ls|
{
    if ls == [] {}
    else {
        concat_homogeneous_len(ls[1..], len);
    }
}

predicate concat_spec<T>(ls: seq<seq<T>>, x1: nat, x2: nat, len: nat)
    requires forall l | l in ls :: |l| == len
    requires x1 < |ls|
    requires x2 < len
{
    concat_homogeneous_len(ls, len);
    && x1 * len + x2 < len * |ls|
    && concat(ls)[x1 * len + x2] == ls[x1][x2]
}


lemma {:induction ls} concat_homogeneous_spec<T>(ls: seq<seq<T>>, len: nat)
    decreases ls
    requires forall l | l in ls :: |l| == len
    ensures |concat(ls)| == len * |ls|
    ensures forall x1:nat, x2:nat | x1 < |ls| && x2 < len ::
        concat_spec(ls, x1, x2, len)
{
    concat_homogeneous_len(ls, len);
    if ls == [] {}
    else {
        concat_homogeneous_spec(ls[1..], len);
        forall x1:nat, x2:nat | x1 < |ls| && x2 < len
            ensures concat_spec(ls, x1, x2, len)
        {
            if x1 == 0 {
            } else {
                assert concat_spec(ls[1..], x1-1, x2, len);
                // assert concat(ls[1..])[(x1-1) * len + x2] == ls[1..][x1-1][x2];
                // assert (x1-1) * len + x2 == (x1*len + x2) - len;
            }
        }
    }
}

lemma concat_homogeneous_spec1<T>(ls: seq<seq<T>>, x1: nat, x2: nat, len: nat)
    requires forall l | l in ls :: |l| == len
    requires x1 < |ls| && x2 < len
    ensures concat_spec(ls, x1, x2, len)
{
    concat_homogeneous_spec(ls, len);
}

lemma concat_homogeneous_spec_alt<T>(ls: seq<seq<T>>, len: nat)
    requires forall l | l in ls :: |l| == len
    ensures |concat(ls)| == len * |ls|
    ensures forall x: nat | x < len * |ls| ::
        concat(ls)[x] == ls[x / len][x % len]
{
    concat_homogeneous_len(ls, len);
    forall x: nat | x < len * |ls|
        ensures concat_spec(ls, x / len, x % len, len)
        ensures concat(ls)[x] == ls[x / len][x % len]
    {
        div_incr(x, |ls|, len);
        concat_homogeneous_spec1(ls, x/len, x%len, len);
        div_mod_split(x, len);
        assert concat_spec(ls, x/len, x%len, len);
        assert (x/len) * len + (x%len) == x;
        assert concat(ls)[(x/len) * len + (x%len)] == concat(ls)[x];
    }
}

lemma {:induction ls} concat_app1<T>(ls: seq<seq<T>>, x: seq<T>)
    decreases ls
    ensures concat(ls + [x]) == concat(ls) + x
{
    if ls == [] {
    } else {
        concat_app1(ls[1..], x);
        assert (ls + [x])[1..] == ls[1..] + [x];
    }
}

// extracting one full list from a concatnation
lemma concat_homogeneous_one_list<T>(ls: seq<seq<T>>, k: nat, len: nat)
    requires forall l | l in ls :: |l| == len
    requires 1 < len
    requires k < |ls|
    ensures k * len + len <= |concat(ls)|
    ensures concat(ls)[k * len..k*len + len] == ls[k]
{
    concat_homogeneous_spec(ls, len);
    assert k * len + len == (k+1) * len;
    forall i: nat | i < len
        ensures concat(ls)[k * len + i] == ls[k][i]
    {
        assert concat_spec(ls, k, i, len);
    }
}

// map to domain as a set

function method map_domain<K, V>(m: map<K, V>): set<K> {
    set k:K | k in m
}

// prefix_of

predicate prefix_of<T>(s1: seq<T>, s2: seq<T>) {
    |s1| <= |s2| && s1 == s2[..|s1|]
}

lemma prefix_of_concat2<T>(s1: seq<T>, s2: seq<T>, s: seq<T>)
requires prefix_of(s1, s2)
ensures prefix_of(s1, s2 + s)
{
}

lemma prefix_of_refl<T>(s: seq<T>)
ensures prefix_of(s, s)
{
}

lemma prefix_of_refl_inv<T>(s1: seq<T>, s2: seq<T>)
requires prefix_of(s1, s2)
requires |s1| == |s2|
ensures s1 == s2
{
}

lemma prefix_of_app2<T>(s1: seq<T>, s2: seq<T>, n: nat)
requires prefix_of(s1, s2)
requires n <= |s1|
ensures prefix_of(s1[n..], s2[n..])
{
}

// summation

function method sum_nat(xs: seq<nat>): nat
decreases xs
{
    if xs == [] then 0
    else xs[0] + sum_nat(xs[1..])
}

lemma {:induction count} sum_repeat(x: nat, count: nat)
ensures sum_nat(repeat(x, count)) == count * x
{
    reveal_repeat();
}

// NOTE(tej): if you happen to know the proof, then Dafny can automatically
// prove this with just {:induction xs, i} (but not just i or xs or even i, xs)
lemma {:induction xs, i} sum_update(xs: seq<nat>, i:nat, x: nat)
requires i < |xs|
decreases xs
ensures sum_nat(xs[i:=x]) == sum_nat(xs)-xs[i]+x
{
    assert 0 < |xs|;
    if i == 0 {}
    else {
        // assert (xs[i:=x])[1..] == xs[1..][i-1:=x];
        sum_update(xs[1..], i-1, x);
    }
}

// unique

predicate unique<T>(xs: seq<T>)
{
  forall i, j | 0 <= i < |xs| && 0 <= j < |xs| && xs[i] == xs[j] :: i == j
}

lemma unique_extend<T>(xs: seq<T>, x: T)
    requires unique(xs)
    requires x !in xs
    ensures unique(xs + [x])
{}

}
