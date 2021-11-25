include "../machine/machine.dfy"

module LockOrder {
  import opened Machine

  // these are intended to be maintained in sorted order
  type LockHint = seq<uint64>

  const EmptyLockHint: LockHint := []

  function method has_lock(locks: LockHint, h: uint64): bool
  {
    h in locks
  }

  function method insert_lock_hint(locks: LockHint, h: uint64): LockHint
  {
    if locks == [] then [h]
    else if h <= locks[0] then [h] + locks
    else [locks[0]] + insert_lock_hint(locks[1..], h)
  }

  function method insert_lock_hints(locks: LockHint, hs: seq<uint64>): LockHint
    decreases |hs|
  {
    if hs == [] then []
    else insert_lock_hints(insert_lock_hint(locks, hs[0]), hs[1..])
  }

  predicate lock_hints_sorted(locks: LockHint)
  {
    forall i, j | 0 <= i < j < |locks| :: locks[i] <= locks[j]
  }

  // this isn't actually needed for anything
  lemma lemma_insert_lock_hint_preserves_sorted(locks: LockHint, h: uint64)
    requires lock_hints_sorted(locks)
    ensures |insert_lock_hint(locks, h)| == |locks| + 1
    ensures multiset(insert_lock_hint(locks, h)) == multiset(locks + [h])
    ensures lock_hints_sorted(insert_lock_hint(locks, h))
  {
    if locks == [] {}
    else {
      lemma_insert_lock_hint_preserves_sorted(locks[1..], h);
      assert locks == [locks[0]] + locks[1..];
      if h <= locks[0] {}
      else {
        assert insert_lock_hint(locks, h)[0] == locks[0];
        forall i, j | 0 <= i < j < |locks| + 1
          ensures insert_lock_hint(locks, h)[i] <= insert_lock_hint(locks, h)[j]
        {
          if i == 0 {
            assert insert_lock_hint(locks, h)[i] == locks[0];
            assert insert_lock_hint(locks, h)[j] == insert_lock_hint(locks[1..], h)[j-1];
            // TODO: not sure exactly how to finish the proof
            assume false;
          } else {
            // easy
          }
        }
      }
    }
  }
}
