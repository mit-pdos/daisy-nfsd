# Overall proof strategy

## Verified 2PL

In Iris, verify refinement for a 2PL system. The spec is something like a
refinement between Go + 2PL and Go + disk, where the 2PL API has a single
operation `doTransaction(txn)`. The hard part is making `txn` expressive enough
(eg, need to be able to read data, manipulate it, and write it back) but also
have some restrictions (eg, transactions should not be able to share state).
We've implemented the `doTransaction` operation as a language-level
`Atomically(e)` expression, which runs small steps for `e` until termination. We
plan to implement these restrictions with a logical relation that supports only
transaction operations within `e` when `Atomically(e)` appears in the spec
program, which roughly corresponds to `btxn := txn.Begin(); /* do transaction */; btxn.CommitWait(true)`.

Now Dafny has an object for the transaction system which supports `Begin`,
operations within the transaction, and `Commit`. The effect of running this
transaction corresponds to building and then atomically executing a `txn` in the
Coq API. Thus proving the refinement obligations about a collection of methods
in Dafny proves refinement against the 2PL API, and then by some transitivity
argument we can link with the real 2PL implementation and the whole thing has
the right refinement spec.

# Compilation

## Dafny to Go compilation

Native integer types are accessible with `{:nativeType}` on a `newtype` type.

Byte slices are axiomatized as an `{:extern}` class. These have a number of
operations, but notably we don't have a notion of a slice which is a view into
the same memory as another slice (modeling this would require separating
"allocations" from slices, which would be views into allocations). This
simplifies the representation and avoids extra disjointness statements but it
does require a bunch of extra operations and offsets as part of every API.

All external interfaces are also implemented by operating on maps and sequences.
These implementations are never run but check that the spec is non-trivial. This
is especially important because Dafny _will_ exploit a contradictory spec - for
example leaving off `modifies` and specifying `data == old(data) + bs` means
data is both `old(data)` and `bs`, thus asserting those expressions are equal.

The generated code is horrible to read but manageable. It's easy to write
low-performance code: for example, sequences are just too inefficient for
anything of moderate size, and when `nat`s show up in the code they're quite
slow. We have efficient byte slices as an extern interface, but this does mean
that we can't us integer slices (unless we had a separate extern interface for
those). Linear types seem like they would help a lot, but the VeriBetrKV linear
types version of Dafny only supports the C++ backend.
