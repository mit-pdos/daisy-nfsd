#!/usr/bin/env bash

set -eu

cd ~/daisy-nfsd
go build ./cmd/daisy-eval
mkdir -p eval/data/nvme
sudo chown "$USER" /dev/nvme1n1
time ./daisy-eval --dir eval/data/nvme --disk /dev/nvme1n1 --iters 10 bench
time ./daisy-eval --dir eval/data/nvme --disk /dev/nvme1n1 --iters 5 scale --benchtime=5s --threads 36
time ./daisy-eval --dir eval/data/nvme --disk /dev/nvme1n1 --iters 10 --wait 3s largefile
time ./daisy-eval --dir eval/data --disk "/dev/shm/disk.img" --iters 10 bench
time ./daisy-eval --dir eval/data --disk "/dev/shm/disk.img" --iters 10 --wait 3s largefile
