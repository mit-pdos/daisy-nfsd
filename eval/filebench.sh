#!/usr/bin/env bash

set -eu

blue=$(tput setaf 4 || echo)
reset=$(tput sgr0 || echo)

info() {
    echo -e "${blue}$1${reset}" 1>&2
}

if [ ! -d "$DAISY_NFSD_PATH" ]; then
    echo "DAISY_NFSD_PATH is unset" 1>&2
    exit 1
fi
if [ ! -d "$GO_NFSD_PATH" ]; then
    echo "GO_NFSD_PATH is unset" 1>&2
    exit 1
fi

threads=10
if [[ $# -gt 0 ]]; then
    threads="$1"
fi

bench=$2

# the path to store the disk file in (use this to run the benchmarks on a real
# drive)
disk_path="$HOME"

fbenchrunner=$DAISY_NFSD_PATH/eval/run-filebench.sh

cd "$DAISY_NFSD_PATH"
info "DaisyNFS filebench scalability"
echo "fs=dnfs"
./bench/run-daisy-nfsd.sh -disk "$disk_path"/disk.img "$fbenchrunner" "$threads" "$bench"

cd "$GO_NFSD_PATH"
echo 1>&2
info "GoNFS filebench scalability"
echo "fs=gonfs"
./bench/run-go-nfsd.sh -disk "$disk_path"/disk.img "$fbenchrunner" "$threads" "$bench"

echo 1>&2
info "Linux filebench scalability"
echo "fs=linux"
./bench/run-linux.sh -disk "$disk_path"/disk.img "$fbenchrunner" "$threads" "$bench"
