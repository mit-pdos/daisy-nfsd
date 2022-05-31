#!/usr/bin/env bash

set -eu

cd ~/daisy-nfsd
go build ./cmd/daisy-eval

nvme=/dev/nvme1n1
mem=/dev/shm/disk.img

paper_fss=daisy-nfsd,daisy-nfsd-seq-txn,linux,linux-ordered
paper_scale_fss=daisy-nfsd,daisy-nfsd-seq-txn,linux
scale_fss=daisy-nfsd,daisy-nfsd-seq-wal,daisy-nfsd-seq-txn,linux

mkdir -p eval/data/nvme
sudo chown "$USER" "$nvme"

# thesis experiments
time ./daisy-eval --filesystems extended --dir eval/data/nvme --disk "$nvme" --iters 5 extended-bench --benchtime=20s --par=25
time ./daisy-eval --filesystems extended --dir eval/data --disk "$mem" --iters 5 extended-bench --benchtime=20s --par=25

time ./daisy-eval --filesystems daisy-nfsd,linux --dir eval/data --disk "$mem" --iters 10 bench --benchtime=20s

time ./daisy-eval --filesystems "$scale_fss" --dir eval/data/nvme --disk "$nvme" --iters 1 scale --benchtime=30s --threads 36
time ./daisy-eval --filesystems daisy-nfsd,linux --dir eval/data --disk "$mem" --iters 1 scale --benchtime=30s --threads 36

# for paper
time ./daisy-eval --filesystems "$paper_fss" --dir eval/data/nvme --disk "$nvme" --iters 10 extended-bench --benchtime=20s --par=36
time ./daisy-eval --filesystems "$paper_scale_fss" --dir eval/data/nvme --disk "$nvme" --iters 1 scale --benchtime=30s --threads 36
# artifact appendix: in-memory versions of above
time ./daisy-eval --filesystems "$paper_fss" --dir eval/data --disk "$mem" --iters 10 extended-bench --benchtime=20s --par=36
time ./daisy-eval --filesystems "$paper_scale_fss" --dir eval/data --disk "$mem" --iters 1 scale --benchtime=30s --threads 36

# some other things to try
#time ./daisy-eval --filesystems durability --dir eval/data/nvme --disk "$nvme" --iters 10 --wait 3s largefile
