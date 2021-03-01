# dafny-jrnl

[[![CI](https://github.com/mit-pdos/dafny-jrnl/actions/workflows/main.yml/badge.svg)](https://github.com/mit-pdos/dafny-jrnl/actions/workflows/main.yml)](https://github.com/mit-pdos/dafny-jrnl/actions/workflows/main.yml)

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

[File-system example](./src/Dafny/examples/fs/dir_fs.dfy)

## Compiling

Run `make verify` to verify everything and `make compile` to compile
the file-system and bank examples to Go (the generated code goes into
`dafnygen/`).

You'll need Dafny 3 on your $PATH. Compilation additionally depends on
goimports to remove unused imports:

```sh
go get golang.org/x/tools/cmd/goimports
```

Then you can run some sanity tests over the bank and file-system examples.
These are ordinary Go tests that import the code generated from Dafny and
run it, linking with [goose-nfsd](https://github.com/mit-pdos/goose-nfsd),
specifically with its `twophase` package. To run these tests,
after compiling with `make compile`, run:

```sh
go test -v ./tests
```

## Running the NFS server

You'll need some basic utilities: the rpcbind service to tell the server what
port to run on, and the NFS client utilities to mount the file system. On Arch
Linux these are available using `pacman -S rpcbind nfs-utils` and on Ubuntu you
can use `apt-get install rpcbind nfs-common`.

You might need to start the rpcbind service with `systemctl start rpcbind`. The
`rpcinfo -p` command is useful for verifying that an `rpcbind` service is
running on port 111.

Now run `go run ./cmd/dafny-nfsd` to start the server and `sudo mount localhost:/ /mnt/x` to mount it using the Linux NFS client.

On macOS you already have `rpcbind` and the NFS client utilities, but you'll
need to start a couple services with:

```
sudo launchctl start com.apple.rpcbind
sudo launchctl start com.apple.lockd
```

## Developing

We provide a library at `dafny_go` that exports some external APIs that are
axiomatized using `{:extern}` modules, classes, and methods in Dafny. Some of
these are core primitives, like `[]byte` and little-endian encoding, while the
big one is the `jrnl` package which interfaces between Dafny and
`github.com/mit-pdos/goose-nfsd/txn`.

The support library is trusted and hence its agreement with the Dafny spec is
important.

You can run tests for this support library with `go test`:

```sh
go test ./dafny_go/...
```
