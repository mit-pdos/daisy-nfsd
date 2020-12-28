# Dafny to Go compilation

TL;DR: it's terrible

Difficult to impossible to access native types (eg, native arithmetic or real
byte slices), so we can't interface with our normal code. It might be possible
to extract some code and then hook it up to the real API externally, but it
would do all sorts of strange things internally.

# Overall proof strategy

## Verified 2PL

In Iris, verify refinement for a 2PL system. The spec is something like a
refinement between Go + 2PL and Go + disk, where the 2PL API has a single
operation `doTransaction(txn)`. The hard part is making `txn` expressive enough
(eg, need to be able to read data, manipulate it, and write it back) but also
have some restrictions (eg, transactions should not be able to share state).

Now Dafny has an object for the transaction system which supports `Begin`,
operations within the transaction, and `Commit`. The effect of running this
transaction corresponds to building and then atomically executing a `txn` in the
Coq API. Thus proving the refinement obligations about a collection of methods
in Dafny proves refinement against the 2PL API, and then by some transitivity
argument we can link with the real 2PL implementation and the whole thing has
the right refinement spec.

## Dafny for sequential WP proofs

Client needs to set up locking. Dafny only proves the sequential part of the
overall WPC proof, using lock operations to get access to lock invariant state
(represented as Dafny objects). The final theorem is one in Perennial, but we
don't formalize it because we would then need both sides to agree on the lock
invariants.

## Verified journal with lifting

Prove a refinement spec for our current code, where client needs to have a
locking discipline. API has ghost operations for moving ownership around, which
it must do to avoid undefined behavior. Spec out concurrent separation logic
locks for Dafny to get access to ownership, which it then moves around with the
ghost operations.
