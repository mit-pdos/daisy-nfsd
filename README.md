# dafny-jrnl

Verifying crash-safe, concurrent code with sequential proofs. The goal is to
connect goose-nfsd's verified journal with sequential verification in Dafny: the
idea is that the journal should make reasoning sequential, in which case we can
prove applications correct using only sequential reasoning in a productive proof
system like Dafny while carrying out the complicated concurrency and
crash-safety reasoning in Perennial.
