# DafnyNFS evaluation

These scripts use some environment variables that point to a few repositories:

```
export GOOSE_NFSD_PATH=~/goose-nfsd
export DAFNY_NFSD_PATH=~/dafny-nfsd
export XV6_PATH=~/xv6-public
export LTP_PATH=~/ltp
```

You'll need to clone
[mit-pdos/goose-nfsd](https://github.com/mit-pdos/goose-nfsd),
[mit-pdos/xv6-public](https://github.com/mit-pdos/xv6-public), and
[linux-test-project/ltp](https://github.com/linux-test-project/ltp) (this last
one is only needed to run the stress tests).

This repo is [mit-pdos/dafny-nfsd](https://github.com/mit-pdos/dafny-nfsd).

## smallfile, largefile, and app benchmarks

Run `./bench.sh | tee data/bench-raw.txt`. Then `./bench.py data/bench-raw.txt`
will produce a file `data/bench.data`.

By default runs up to 10 cores; you can set this with `./bench.sh 10` for example.

## smallfile scalability on a disk

Run `./scale.sh | tee data/scale-raw.txt`. Then `./scale.py data/scale-raw.txt`
will produce files for each system in `data/{dnfs,gnfs,linux-nfs}.data`.

This hosts the disk in a file in your home directory, so that file system
determines what disk you're using. You can change a local variable in
`./scale.sh` if you need to change this.

## Plotting

You can run `./plot.sh` to run the Python post-processing and gnuplot all at once.

## stress tests

Run `./scale.sh` to run the fsstress and fsx-linux tests. You'll need to clone
ltp and compile it; the script will give you the right commands.

The default number of iterations runs each suite for about 10 seconds. To run
longer, run something like `./scale.sh 10`, which will scale the default
iteration counts by 10.
