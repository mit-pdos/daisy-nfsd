# DaisyNFS evaluation

These scripts use some environment variables that point to a few repositories:

```
export GO_NFSD_PATH=~/go-nfsd
export DAISY_NFSD_PATH=~/daisy-nfsd
export XV6_PATH=~/xv6-public
export LTP_PATH=~/ltp
```

You'll need to clone
[mit-pdos/go-nfsd](https://github.com/mit-pdos/go-nfsd),
[mit-pdos/xv6-public](https://github.com/mit-pdos/xv6-public), and
[linux-test-project/ltp](https://github.com/linux-test-project/ltp) (this last
one is only needed to run the stress tests).

This repo is [mit-pdos/daisy-nfsd](https://github.com/mit-pdos/daisy-nfsd).

These instructions assume you've compiled the evaluation driver with `go build ./cmd/daisy-eval`.

## smallfile, largefile, and app benchmarks

Run `daisy-eval -i eval/data bench`. Then `./eval/eval.py -i eval/data bench`
will produce a file `eval/data/bench.data`.

## smallfile scalability on a disk

Run `daisy-eval -i eval/data bench`. Then `./eval/eval.py -i eval/data scale`
will produce files for each system in `data/{daisy-nfsd,go-nfsd,linux}.data`.

The `daisy-eval` driver has an argument to set the disk file.

## Plotting

You can run `./plot.sh` to run the Python post-processing and gnuplot all at once.

## stress tests

Run `./tests.sh` to run the fsstress and fsx-linux tests. You'll need to clone
ltp and compile it; the script will give you the right commands.

The default number of iterations runs each suite for about 10 seconds. To run
longer, run something like `./tests.sh 10`, which will scale the default
iteration counts by 10.
