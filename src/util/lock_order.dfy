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

  // is it safe to acquire l, with locks held?
  function method safe_lock(locks: LockHint, l: uint64): bool
  {
    locks == [] || has_lock(locks, l) || l > locks[|locks|-1]
  }

  function method insert_lock_hint(locks: LockHint, h: uint64): LockHint
  {
    if locks == [] then [h]
    else if h < locks[0] then [h] + locks
    else if h == locks[0] then locks // already present
    else [locks[0]] + insert_lock_hint(locks[1..], h)
  }

  function method insert_lock_hints(locks: LockHint, hs: seq<uint64>): LockHint
    decreases |hs|
  {
    if hs == [] then locks
    else insert_lock_hints(insert_lock_hint(locks, hs[0]), hs[1..])
  }

  predicate lock_hints_sorted(locks: LockHint)
  {
    forall i, j | 0 <= i < j < |locks| :: locks[i] <= locks[j]
  }

  lemma lemma_insert_lock_hint_size(locks: LockHint, h: uint64)
    ensures |insert_lock_hint(locks, h)| <= |locks| + 1
  {
  }

  lemma lemma_insert_lock_hints_sanity(locks: LockHint, h: uint64)
    ensures insert_lock_hints(locks, [h]) == insert_lock_hint(locks, h)
  {
  }
}
