#!/usr/bin/env bash

set -eu

cd ~/daisy-nfsd
go build ./cmd/daisy-eval

mkdir -p eval/data/nvme
sudo chown "$USER" /dev/nvme1n1
# time ./daisy-eval --dir eval/data/nvme --disk /dev/nvme1n1 --iters 10 bench
# time ./daisy-eval --dir eval/data --disk "/dev/shm/disk.img" --iters 10 bench
# time ./daisy-eval --dir eval/data/nvme --disk /dev/nvme1n1 --iters 1 scale --benchtime=5s --threads 36
# time ./daisy-eval --dir eval/data/nvme --disk /dev/nvme1n1 --iters 10 --wait 3s largefile
# time ./daisy-eval --dir eval/data --disk "/dev/shm/disk.img" --iters 10 --wait 3s largefile

# for p in orig no-append-merge no-install-merge no-flush global-wal-lock global-txn-lock
for p in no-flush-no-append-merge no-flush-no-install-merge no-flush-no-merge
do
	mkdir -p "eval/data/patch/${p}"
	mkdir -p "eval/data/nvme/patch/${p}"
	time ./daisy-eval --dir "eval/data/patch/${p}" --disk "/dev/shm/disk.img" --iters 10 --jrnlpatch "eval/patches/${p}.patch" bench
	time ./daisy-eval --dir "eval/data/nvme/patch/${p}" --disk /dev/nvme1n1 --iters 10 --jrnlpatch "eval/patches/${p}.patch" bench
done
