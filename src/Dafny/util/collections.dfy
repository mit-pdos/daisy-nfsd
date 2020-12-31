// repeat

function method {:opaque}
repeat<T>(x: T, count: nat): (xs:seq<T>) decreases count
ensures |xs| == count && forall i :: 0 <= i < |xs| ==> xs[i] == x
{
    if count == 0 then [] else [x] + repeat(x, count-1)
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
