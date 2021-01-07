# dafny-jrnl

[![verify](https://github.com/mit-pdos/dafny-jrnl/workflows/verify/badge.svg)](https://github.com/mit-pdos/dafny-jrnl/actions?query=workflow%3Averify)

Verifying crash-safe, concurrent code with sequential proofs. The goal is to
connect goose-nfsd's verified journal with sequential verification in Dafny: the
idea is that the journal should make reasoning sequential, in which case we can
prove applications correct using only sequential reasoning in a productive proof
system like Dafny while carrying out the complicated concurrency and
crash-safety reasoning in Perennial.

## Status

[Notes on research directions](./research.md)

[Spec for journal interface, assuming 2PL](./src/Dafny/jrnl/jrnl.s.dfy)

[Bank example](./src/Dafny/examples/bank.dfy)
