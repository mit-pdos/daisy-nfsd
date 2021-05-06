#!/bin/bash

# run various performance benchmarks

set -eu

blue=$(tput setaf 4 || echo)
reset=$(tput sgr0 || echo)

info() {
  echo -e "${blue}$1${reset}" 1>&2
}

if [ ! -d "$DAFNY_NFSD_PATH" ]; then
    echo "DAFNY_NFSD_PATH is unset" 1>&2
    exit 1
fi
if [ ! -d "$GOOSE_NFSD_PATH" ]; then
    echo "GOOSE_NFSD_PATH is unset" 1>&2
    exit 1
fi
if [ ! -d "$XV6_PATH" ]; then
    echo "XV6_PATH is unset" 1>&2
    exit 1
fi

startthreads=1
threads=10
if [[ $# -gt 0 ]]; then
    threads="$1"
fi

info "Using $threads threads"

cd "$GOOSE_NFSD_PATH"
go build ./cmd/fs-smallfile
go build ./cmd/fs-largefile

cd "$DAFNY_NFSD_PATH"

info "DafnyNFS"
echo "fs=dnfs"
./bench/run-dafny-nfs.sh "$GOOSE_NFSD_PATH"/fs-smallfile -start="$startthreads" -threads="$threads"
./bench/run-dafny-nfs.sh "$GOOSE_NFSD_PATH"/fs-largefile
./bench/run-dafny-nfs.sh "$GOOSE_NFSD_PATH"/bench/app-bench.sh "$XV6_PATH" /mnt/nfs

cd "$GOOSE_NFSD_PATH"

echo 1>&2
info "GoNFS"
echo "fs=gonfs"
./bench/run-goose-nfs.sh "$GOOSE_NFSD_PATH"/fs-smallfile -start="$startthreads" -threads="$threads"
./bench/run-goose-nfs.sh "$GOOSE_NFSD_PATH"/fs-largefile
./bench/run-goose-nfs.sh "$GOOSE_NFSD_PATH"/bench/app-bench.sh "$XV6_PATH" /mnt/nfs

echo 1>&2
info "Linux ext4 over NFS"
echo "fs=linux"
./bench/run-linux.sh "$GOOSE_NFSD_PATH"/fs-smallfile -start="$startthreads" -threads="$threads"
./bench/run-linux.sh "$GOOSE_NFSD_PATH"/fs-largefile
./bench/run-linux.sh "$GOOSE_NFSD_PATH"/bench/app-bench.sh "$XV6_PATH" /mnt/nfs
