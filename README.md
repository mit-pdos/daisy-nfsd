# DaisyNFS

[![CI](https://github.com/mit-pdos/daisy-nfsd/actions/workflows/main.yml/badge.svg)](https://github.com/mit-pdos/daisy-nfsd/actions/workflows/main.yml)

A verified crash-safe, concurrent NFS server. The idea is to make operations
atomic with a verified transaction system from
[GoTxn](https://github.com/mit-pdos/go-journal), and then verify the atomic
behavior of each operation in Dafny. The atomicity justifies using sequential
proofs in Dafny to reason about the body of each transaction, which we prove
implements an NFS server. This proof strategy combines interactive theorem
proving in Perennial, to reason about the tricky concurrency and crash safety in
the transaction system, with automated proofs in Dafny for the file-system code.

## Architecture

There are three main components:

- The Dafny file-system implementation in [`src/fs`](src/fs/)
- The Go interfaces assumed by the Dafny code implemented in
  [`dafny_go`](dafny_go/) (the jrnl API is a thin wrapper around the
  github.com/mit-pdos/go-journal/txn package).
- The NFS server binary that calls the verified Dafny code is implemented
  between [`nfsd`](nfsd/) and [`cmd/daisy-nfsd`](cmd/daisy-nfsd/).

The Dafny proof is split into three parts:

- external interfaces only assumed in Dafny via `{:extern}`:
  [`src/jrnl`](src/jrnl) (the transaction system) and
  [`src/machine`](src/machine) (Go primitives)
- verified helper libraries in [`src/util`](src/util) that would basically be in
  a decent Dafny standard library
- the actual file-system proof, documented in its own [README](src/fs/README.md)

At the top level of the repo we also have various scripts. [`eval`](eval/) and
[`bench`](bench/) have scripts to run performance experiments (see the [eval
README](eval/README.md) for more details). [`artifact`](artifact/) has an older
setup for running the evaluation on a VM; these days we use an AWS setup.
[`etc`](etc/) has miscellaneous scripts used for debugging and to implement
continuous integration.

## Compiling

Run `make` to compile and verify everything, or `make compile` to just compile
from Dafny to Go. Then you can build the server with `go build ./cmd/daisy-nfsd`.

You'll need Dafny 4:

- On Arch Linux you can get `dafny-bin` from the AUR
- On macOS use `brew install dafny`
- For other systems the easiest solution is to download a binary release from
  <https://github.com/dafny-lang/dafny/releases>, extract it, and add it to your
  $PATH (this is what we have to do in CI, which runs on Ubuntu 22.04).

Compilation additionally depends on `goimports` to remove unused imports:

```sh
go install golang.org/x/tools/cmd/goimports@latest
```

Then you can run some sanity tests over the bank and file-system examples.
These are ordinary Go tests that import the code generated from Dafny and
run it, linking with [go-nfsd](https://github.com/mit-pdos/go-nfsd),
specifically with its `twophase` package. To run these tests,
after compiling with `make compile`, run:

```sh
go test -v ./tests
```

## Running the NFS server

### Linux

You'll need some basic utilities: the rpcbind service to tell the server what
port to run on, and the NFS client utilities to mount the file system. On Arch
Linux these are available using `pacman -S rpcbind nfs-utils` and on Ubuntu you
can use `apt-get install rpcbind nfs-common`.

You might need to start the rpcbind service with `systemctl start rpcbind`. It
seems to help if you also run `systemctl start rpc-statd` (it should be
auto-launched when needed, though). The `rpcinfo -p` command is useful for
verifying that an `portmapper` service is running on port 111.

Now run `go run ./cmd/daisy-nfsd` to start the server (with an in-memory disk)
and `sudo mount localhost:/ /mnt/nfs` to mount it using the Linux NFS client.

If you encounter an error with the message `Too many levels of symbolic links.`,
don't panic! This is actually due to a bug in the Linux NFS client, which was
fixed in December 2020 in [commit
3b2a09f127e02](https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/commit/?id=3b2a09f127e025674945e82c1ec0c88d6740280e).
If a READDIR result was larger than a page, Linux would simply discard the extra
data, resulting in a corrupted response. You'll need at least version 5.11 of
the kernel to get the fix (you can check what you have with `uname -r`).

### macOS

On macOS you already have `rpcbind` and the NFS client utilities, but you'll
need to start a couple services with:

```sh
sudo launchctl start com.apple.rpcbind
sudo launchctl start com.apple.lockd
```

You can mount with `sudo mount localhost:/ /mnt/nfs` as for Linux, or without
becoming root in Finder with Go > Connect to server... and connecting to
`nfs://localhost/`.

## Developing

We provide a library at `dafny_go` that exports some external APIs that are
axiomatized using `{:extern}` modules, classes, and methods in Dafny. Some of
these are core primitives, like `[]byte` and little-endian encoding, while the
big one is the `jrnl` package which interfaces between Dafny and
`github.com/mit-pdos/go-nfsd/txn`.

The support library is trusted and hence its agreement with the Dafny spec is
important.

You can run tests for this support library with `go test`:

```sh
go test ./dafny_go/...
```

## Checking verification performance

To time verification and analyze the results easily, we have a script to process timing from Dafny's `/trace` option. Use it with the following fish function:

```fish
function dafny_time
  set -l file $argv[1]
  dafny /timeLimit:10 /compile:0 /arith:5 /noNLarith /trace $file $argv[2..-1] > .timing.prof
  cat .timing.prof | ./etc/summarize-timing
end
```

The timing infrastructure itself is implemented as a library in `etc/`. It even
has tests, which you can run with `pytest`.
