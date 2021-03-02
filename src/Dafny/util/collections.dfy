include "../nonlin/arith.dfy"

module Collections
{
import opened Arith

lemma seq_ext_eq<T>(xs: seq<T>, ys: seq<T>)
  requires |xs| == |ys|
  requires forall i :: 0 <= i < |xs| ==> xs[i] == ys[i]
  ensures xs == ys
{}

// workaround for Dafny bug https://github.com/dafny-lang/dafny/issues/1113
function to_seq<T>(s: seq<T>): seq<T> { s }

// sequence indexing

lemma double_subslice<T>(xs: seq<T>, a: nat, b: nat, c: nat, d: nat)
    requires a <= b <= |xs|
    requires c <= d <= (b-a)
    ensures xs[a..b][c..d] == xs[a+c..a+d]
{
    // consequence of the bounds that make xs[..a+d] well-formed
    assert d + a <= b;
    assert xs[a..b] == xs[a..][..(b-a)];
}

lemma app_assoc<T>(xs: seq<T>, ys: seq<T>, zs: seq<T>)
    ensures (xs + ys) + zs == xs + (ys + zs)
{}

lemma split_rejoin<T>(xs: seq<T>, n: int)
    requires 0 <= n < |xs|
    ensures xs == xs[..n] + xs[n..]
{}

// this is a useful way to use double_subslice automatically in a controlled way
// that generally works, because it has such a specific trigger
//
// see http://leino.science/papers/krml265.html for some more ideas
lemma double_subslice_auto<T>(xs: seq<T>)
    ensures forall a: nat, b: nat, c: nat, d: nat {:trigger xs[a..b][c..d]} |
        a <= b <= |xs| && c <= d <= (b-a) ::
        xs[a..b][c..d] == xs[a+c..a+d]
{
    forall a: nat, b: nat, c: nat, d: nat |
        a <= b <= |xs| && c <= d <= (b-a)
        ensures xs[a..b][c..d] == xs[a+c..a+d]
    {
        double_subslice(xs, a, b, c, d);
    }
}

// fmap over sequences

function method {:opaque}
seq_fmap<T,U>(f: T -> U, xs: seq<T>): (ys:seq<U>) decreases xs
ensures |ys| == |xs| && forall i :: 0 <= i < |xs| ==> ys[i] == f(xs[i])
{
    if xs == [] then [] else [f(xs[0])] + seq_fmap(f, xs[1..])
}

lemma seq_fmap_compose<T,U,V>(f: T -> U, g: U -> V, xs: seq<T>)
    ensures seq_fmap(g, seq_fmap(f, xs)) == seq_fmap(x => g(f(x)), xs)
{}

// filter
function method seq_filter<T>(p: T -> bool, xs: seq<T>): (ys:seq<T>)
    ensures |ys| <= |xs| && forall y :: y in ys ==> p(y) && y in xs
{
    if xs == [] then []
    else (if p(xs[0]) then [xs[0]] else []) + seq_filter(p, xs[1..])
}

lemma seq_filter_size<T>(p: T -> bool, xs: seq<T>)
    ensures |seq_filter(p, xs)| == count_matching(p, xs)
{}

// find_first
function method find_first<T>(p: T -> bool, xs: seq<T>): (i:nat)
    ensures i < |xs| ==> p(xs[i])
{
    if xs == [] then 0
    else if p(xs[0]) then 0 as nat else 1 + find_first(p, xs[1..])
}

lemma {:induction xs} find_first_complete<T>(p: T -> bool, xs: seq<T>)
    ensures find_first(p, xs) <= |xs|
    ensures forall k:nat | k < find_first(p, xs) :: !p(xs[k])
{}

lemma find_first_characterization<T>(p: T -> bool, xs: seq<T>, i: nat)
    requires i < |xs| ==> p(xs[i])
    requires i <= |xs|
    requires forall k:nat | k < i :: !p(xs[k])
    ensures i == find_first(p, xs)
{
    if 0 < |xs| {
        if p(xs[0]) {}
        else {
            find_first_characterization(p, xs[1..], i-1);
        }
    }
}

// count matching a predicate
function method count_matching<T>(p: T -> bool, xs: seq<T>): (i:nat)
    ensures i <= |xs|
{
    if xs == [] then 0
    else (if p(xs[0]) then 1 else 0) + count_matching(p, xs[1..])
}

lemma {:induction xs1} count_matching_app<T>(p: T -> bool, xs1: seq<T>, xs2: seq<T>)
    ensures count_matching(p, xs1 + xs2) == count_matching(p, xs1) + count_matching(p, xs2)
{
    if xs1 == [] {
        assert xs1 + xs2 == xs2;
    } else {
        assert (xs1 + xs2)[1..] == xs1[1..] + xs2;
    }
}

// repeat

function method repeat<T>(x: T, count: nat): (xs:seq<T>)
{
    seq(count, _ => x)
}

lemma repeat_seq_fmap_auto<T, U>()
    ensures forall f: T -> U, x:T, count {:trigger seq_fmap(f, repeat(x, count))} :: seq_fmap(f, repeat(x, count)) == repeat(f(x), count)
{}

// equation for repeat for induction on count
lemma repeat_unfold<T>(x: T, count: nat)
    requires 0 < count
    ensures repeat(x, count) == [x] + repeat(x, count-1)
{}

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

lemma {:induction ls1} concat_app<T>(ls1: seq<seq<T>>, ls2: seq<seq<T>>)
    ensures concat(ls1 + ls2) == concat(ls1) + concat(ls2)
{
    if ls1 == [] {
        assert [] + ls2 == ls2;
    } else {
        assert (ls1 + ls2)[1..] == ls1[1..] + ls2;
        concat_app(ls1[1..], ls2);
    }
}

lemma {:induction ls} concat_homogeneous_len<T>(ls: seq<seq<T>>, len: nat)
    requires forall l | l in ls :: |l| == len
    ensures |concat(ls)| == len * |ls|
{
    if ls == [] {}
    else {
        concat_homogeneous_len(ls[1..], len);
        calc {
            |ls[0] + concat(ls[1..])|;
            len + |concat(ls[1..])|;
            len + len*(|ls|-1);
            { mul_distr_add_l(len, |ls|, -1); }
            len * |ls|;
        }
    }
}

predicate concat_spec<T>(ls: seq<seq<T>>, x1: nat, x2: nat, len: nat)
    requires forall l | l in ls :: |l| == len
    requires x1 < |ls|
    requires x2 < len
{
    concat_homogeneous_len(ls, len);
    mul_positive(x1, len);
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
                mul_positive(x1-1, len);
                assert concat(ls[1..])[(x1-1) * len + x2] == ls[1..][x1-1][x2];
                mul_distr_add_r(x1, -1, len);
                assert (x1-1) * len + x2 == (x1*len + x2) - len;
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
        && 0 <= x/len < |ls|
        && concat(ls)[x] == ls[x / len][x % len]
{
    concat_homogeneous_len(ls, len);
    forall x: nat | x < len * |ls|
        ensures concat_spec(ls, x / len, x % len, len)
        ensures 0 <= x/len < |ls|
        ensures concat(ls)[x] == ls[x / len][x % len]
    {
        div_incr(x, |ls|, len);
        div_positive(x, len);
        concat_homogeneous_spec1(ls, x/len, x%len, len);
        div_mod_split(x, len);
        assert concat_spec(ls, x/len, x%len, len);
        assert (x/len) * len + (x%len) == x;
        assert concat(ls)[(x/len) * len + (x%len)] == concat(ls)[x];
    }
}

lemma {:induction ls} concat_in<T>(ls: seq<seq<T>>, x: T)
    ensures x in concat(ls) <==> exists i:nat :: i < |ls| && x in ls[i]
{}

lemma concat_in_intro<T>(ls: seq<seq<T>>, x: T, i: nat)
    requires i < |ls|
    requires x in ls[i]
    ensures x in concat(ls)
{
    concat_in(ls, x);
}

lemma {:induction ls} concat_in_elim<T>(ls: seq<seq<T>>, x: T) returns (i: nat)
    requires x in concat(ls)
    ensures i < |ls| && x in ls[i]
{
    concat_in(ls, x);
    i :| i < |ls| && x in ls[i];
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
    ensures 0 <= k*len
    ensures k * len + len <= |concat(ls)|
    ensures concat(ls)[k * len..k*len + len] == ls[k]
{
    mul_positive(k, len);
    mul_distr_add_r(k, 1, len);
    mul_add_bound(k, 1, |ls|, len);
    mul_r_incr(k+1, |ls|, len);
    concat_homogeneous_spec(ls, len);
    forall i: nat | i < len
        ensures concat(ls)[k * len + i] == ls[k][i]
    {
        assert concat_spec(ls, k, i, len);
    }
}

lemma concat_repeat<T>(x: T, count1: nat, count2: nat)
    ensures 0 <= count2*count1
    ensures concat(repeat(repeat(x, count1), count2)) == repeat(x, count2*count1)
{
    mul_positive(count1, count2);
    concat_homogeneous_spec_alt(repeat(repeat(x, count1), count2), count1);
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
    if count > 0 {
        repeat_unfold(x, count);
    }
    mul_distr_sub_r(count, 1, x);
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
  forall i, j | 0 <= i < |xs| && 0 <= j < |xs| :: xs[i] == xs[j] ==> i == j
}

lemma unique_extend<T>(xs: seq<T>, x: T)
    requires unique(xs)
    requires x !in xs
    ensures unique(xs + [x])
{}

// without_last, last

function without_last<T>(xs: seq<T>): seq<T>
    requires 0 < |xs|
{
    xs[..|xs|-1]
}

function last<T>(xs: seq<T>): T
    requires 0 < |xs|
{
    xs[|xs|-1]
}

lemma concat_split_last<T>(xs: seq<seq<T>>)
    requires 0 < |xs|
    ensures concat(xs) == concat(without_last(xs)) + last(xs)
{
    assert xs == without_last(xs) + [last(xs)];
    concat_app1(without_last(xs), last(xs));
}

// splice (insert sequence)
function method splice<T>(xs: seq<T>, off: nat, ys: seq<T>): (xs':seq<T>)
    requires off + |ys| <= |xs|
    ensures |xs'| == |xs|
{
    xs[..off] + ys + xs[off+|ys|..]
}

lemma splice_get_i<T>(xs: seq<T>, off: nat, ys: seq<T>, i: nat)
    requires off + |ys| <= |xs|
    requires i < |xs|
    ensures splice(xs, off, ys)[i] == if (off <= i < off + |ys|) then ys[i-off] else xs[i]
{}

lemma splice_get_ys<T>(xs: seq<T>, off: nat, ys: seq<T>)
    requires off + |ys| <= |xs|
    ensures splice(xs, off, ys)[off..off+|ys|] == ys
{}

lemma splice_at_0<T>(xs: seq<T>, ys: seq<T>)
    requires |ys| <= |xs|
    ensures splice(xs, 0, ys) == ys + xs[|ys|..]
{}

lemma splice_till_end<T>(xs: seq<T>, off: nat, ys: seq<T>)
    requires off + |ys| == |xs|
    ensures splice(xs, off, ys) == xs[..off] + ys
{}

lemma splice_prefix_comm<T>(xs: seq<T>, off: nat, ys: seq<T>, max: nat)
    requires off + |ys| <= max <= |xs|
    ensures splice(xs, off, ys)[..max] == splice(xs[..max], off, ys)
{}

lemma splice_prefix_comm_auto<T>(xs: seq<T>)
    ensures forall off: nat, ys: seq<T>, max: nat {:trigger {splice(xs, off, ys)[..max]}}
        | off + |ys| <= max <= |xs| ::
        splice(xs, off, ys)[..max] == splice(xs[..max], off, ys)
{}

lemma concat_homogeneous_subslice<T>(xs: seq<seq<T>>, start: nat, end: nat, len: nat)
    requires start <= end <= |xs|
    requires 0 < len
    requires forall l | l in xs :: |l| == len
    ensures 0 <= start*len <= end*len <= |concat(xs)| == len*|xs|
    ensures concat(xs[start..end]) == concat(xs)[start*len..end*len]
{
    assert 0 <= start*len <= end*len <= |concat(xs)| == len*|xs| by {
        concat_homogeneous_len(xs, len);
        mul_positive(start, len);
        mul_positive(end, len);
        mul_r_incr(start, end, len);
        mul_r_incr(end, |xs|, len);
    }
    assert xs == xs[..start] + xs[start..end] + xs[end..];
    assert concat(xs) == concat(xs[..start]) + concat(xs[start..end]) + concat(xs[end..]) by {
        concat_app(xs[..start] + xs[start..end], xs[end..]);
        concat_app(xs[..start], xs[start..end]);
    }
    concat_homogeneous_len(xs[..start], len);
    concat_homogeneous_len(xs[start..end], len);
    concat_homogeneous_len(xs[end..], len);
    assert |concat(xs[..start])| == start*len;
    assert |concat(xs[start..end])| == end*len - start*len by {
        assert |xs[start..end]| == end - start;
        Arith.mul_distr_sub_r(end, start, len);
    }
}

lemma concat_homogeneous_prefix<T>(xs: seq<seq<T>>, end: nat, len: nat)
    requires end <= |xs|
    requires 0 < len
    requires forall l | l in xs :: |l| == len
    ensures 0 <= end*len <= |concat(xs)| == len*|xs|
    ensures concat(xs[..end]) == concat(xs)[..end*len]
{
    concat_homogeneous_subslice(xs, 0, end, len);
}

lemma concat_homogeneous_suffix<T>(xs: seq<seq<T>>, start: nat, len: nat)
    requires start <= |xs|
    requires 0 < len
    requires forall l | l in xs :: |l| == len
    ensures 0 <= start*len <= |concat(xs)| == len*|xs|
    ensures concat(xs[start..]) == concat(xs)[start*len..]
{
    concat_homogeneous_subslice(xs, start, |xs|, len);
}

lemma concat_homogeneous_splice_one<T>(xs: seq<seq<T>>, off: nat, ys: seq<T>, len: nat)
    requires 0 < len
    requires forall l | l in xs :: |l| == len
    requires |ys| == len
    requires off < |xs|
    ensures 0 <= off*len < off*len+len <= |concat(xs)|
    ensures concat(xs[off:=ys]) == splice(concat(xs), off*len, ys)
{
    concat_homogeneous_len(xs, len);
    assert (off+1)* len == off*len + len by {
        mul_distr_add_r(off, 1, len);
    }
    assert 0 <= off*len < off*len + len <= |concat(xs)| by {
        mul_positive(off, len);
        mul_r_incr(off+1, |xs|, len);
    }
    var l1: seq<T> := concat(xs[off:=ys]);
    var l2: seq<T> := splice(concat(xs), off*len, ys);
    concat_homogeneous_len(xs[off:=ys], len);
    concat_homogeneous_spec_alt(xs, len);
    concat_homogeneous_spec_alt(xs[off:=ys], len);
    forall i:nat | i < |xs|*len
        ensures l1[i] == l2[i]
    {
        assert l1[i] == xs[off:=ys][i / len][i % len];
        if off*len <= i < (off+1)*len {
            Arith.div_mod_spec(i, off, len);
            assert i / len == off;
        } else {
            assert i / len != off by {
                if i < off*len {
                    div_incr(i, off, len);
                } else {
                    assert (off+1)*len <= i;
                    Arith.div_increasing((off+1)*len, i, len);
                    Arith.mul_div_id(off+1, len);
                }
            }
        }
    }
    assert l1 == l2;
}

}
