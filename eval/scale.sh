#!/usr/bin/env bash

set -eu

blue=$(tput setaf 4)
reset=$(tput sgr0)

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

threads=10
if [[ $# -gt 0 ]]; then
    threads="$1"
fi

# the path to store the disk file in (use this to run the benchmarks on a real
# drive)
disk_path="$HOME"

cd "$GOOSE_NFSD_PATH"
go build ./cmd/fs-smallfile
go build ./cmd/fs-largefile

cd "$DAFNY_NFSD_PATH"
info "DafnyNFS smallfile scalability"
echo "fs=dnfs"
./bench/run-dafny-nfs.sh -disk "$disk_path"/disk.img "$GOOSE_NFSD_PATH"/fs-smallfile -threads=$threads

cd "$GOOSE_NFSD_PATH"
echo 1>&2
info "GoNFS smallfile scalability"
echo "fs=gonfs"
./bench/run-goose-nfs.sh -disk "$disk_path"/disk.img "$GOOSE_NFSD_PATH"/fs-smallfile -threads=$threads

echo 1>&2
info "Linux smallfile scalability"
echo "fs=linux"
./bench/run-linux.sh     -disk "$disk_path"/disk.img "$GOOSE_NFSD_PATH"/fs-smallfile -threads=$threads
