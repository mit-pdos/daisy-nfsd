# Overall proof strategy

## Verified 2PL

**current plan**
In Iris, verify refinement for a 2PL system. The spec is something like a
refinement between Go + 2PL and Go + disk, where the 2PL API has a single
operation `doTransaction(txn)`. The hard part is making `txn` expressive enough
(eg, need to be able to read data, manipulate it, and write it back) but also
have some restrictions (eg, transactions should not be able to share state).
We've implemented the `doTransaction` operation as a language-level
`Atomically(e)` expression, which runs small steps for `e` until termination. We
plan to implement these restrictions with a logical relation that supports only
transaction operations within `e` when `Atomically(e)` appears in the spec
program, which roughly corresponds to `btxn := txn.Begin(); /* do transaction */;
btxn.CommitWait(true)`.

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

# Compilation

## Dafny to Go compilation

**current plan**

Native integer types are accessible with `:nativeType`.

Byte slices are axiomatized as an `{:extern}` class.

All external interfaces are also equipped with a feasibility module refining the
spec that "implements" the spec using types like maps and sequences. This module
serves as a check that the spec is non-trivial, which is especially easy to
accidentally do in Dafny due to incorrect `modifies` and `reads` clauses. See
https://github.com/dafny-lang/dafny/wiki/Modeling-External-State-Correctly for a
discussion of approach and the problems it solves.

The generated code is horrible, and possible also low performance.

## Go to Dafny

Follow the same strategy as Goose, translating Go using the jrnl API to Dafny
over the axiomatized interface. We would need Dafny models of all the Go code we
care about; these models will probably be a bit more limited than Goose, so
we'll have slightly less idiomatic and/or efficient use of pointers.

One concern is that the Dafny code needs proof annotations, which we can't
easily write in Go (because it would lack the interactive feedback from Dafny).
I think we will want to do something to take the old Dafny output with
annotations and re-translate while preserving those annotations. In any case we
should be able to snapshot the annotations somewhere since we're modifying
auto-generated code.
