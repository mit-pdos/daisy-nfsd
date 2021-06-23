#!/bin/bash

# Extra DafnyNFSD/GoJournal commit combinations can be tried by passing extra
# arguments after the first.  For example,
#
# > ./bench.sh 1 abc123,xyz456 def123,master
#
# Will, in addition to the standard battery of tests, also run DafnyNFSD with
# commit abc123 using GoJournal with commit xyz456 and
# DafnyNFSD with commit def123 and go-journal master.

# run various performance benchmarks

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
if [ ! -d "$GO_JRNL_PATH" ]; then
    echo "GO_JRNL_PATH is unset" 1>&2
    exit 1
fi
if [ ! -d "$XV6_PATH" ]; then
    echo "XV6_PATH is unset" 1>&2
    exit 1
fi

usage() {
    echo "Usage: $0 [-o | --output OUTFILE]" 1>&2
}

output_file="$DAISY_NFSD_PATH/eval/data/bench-raw.txt"
while [[ "$#" -gt 0 ]]; do
    case "$1" in
        -o | --output)
            shift
            output_file="$1"
            shift
            ;;
        -help | --help)
            usage
            exit 0
            ;;
        -*)
            echo "Unknown option $1" 1>&2
            usage
            exit 0
            ;;
        *)
            break
            ;;
    esac
done
output_file=$(realpath "$output_file")

startthreads=1
threads=10
if [[ $# -gt 0 ]]; then
    threads="$1"
fi

info "Using $threads threads"

shift

cd "$GO_NFSD_PATH"
go build ./cmd/fs-smallfile
go build ./cmd/fs-largefile

if [[ $# -gt 0 ]]; then
    for var in "$@"; do
        echo 1>&2
        IFS="," read -r dnfsver goosever <<<"$var"

        info "DafnyNFS-$dnfsver-$goosever"
        info "Assuming DafnyNFS is using $GO_JRNL_PATH for GoJournal"
        cd "$GO_JRNL_PATH"
        git checkout "$goosever" --quiet

        cd "$DAISY_NFSD_PATH"
        git checkout "$dnfsver" --quiet
        go mod edit -replace github.com/mit-pdos/go-journal="$GO_JRNL_PATH"
        echo "fs=dfns-$dnfsver-$goosever"
        ./bench/run-daisy-nfsd.sh "$GO_NFSD_PATH"/fs-smallfile -start="$startthreads" -threads="$threads"
        ./bench/run-daisy-nfsd.sh "$GO_NFSD_PATH"/fs-largefile
        ./bench/run-daisy-nfsd.sh "$GO_NFSD_PATH"/bench/app-bench.sh "$XV6_PATH" /mnt/nfs
    done

    cd "$DAISY_NFSD_PATH"
    go mod edit -dropreplace github.com/mit-pdos/go-journal
    git checkout main --quiet
    cd "$GO_JRNL_PATH"
    git checkout master --quiet
fi

cd "$DAISY_NFSD_PATH"

do_eval() {
    echo 1>&2
    info "DafnyNFS"
    echo "fs=dnfs"
    ./bench/run-daisy-nfsd.sh -disk "" "$GO_NFSD_PATH"/fs-smallfile -start="$startthreads" -threads="$threads"
    ./bench/run-daisy-nfsd.sh -disk "" "$GO_NFSD_PATH"/fs-largefile
    ./bench/run-daisy-nfsd.sh -disk "" "$GO_NFSD_PATH"/bench/app-bench.sh "$XV6_PATH" /mnt/nfs

    cd "$GO_NFSD_PATH"

    echo 1>&2
    info "GoNFS"
    echo "fs=gonfs"
    ./bench/run-go-nfsd.sh -disk "" "$GO_NFSD_PATH"/fs-smallfile -start="$startthreads" -threads="$threads"
    ./bench/run-go-nfsd.sh -disk "" "$GO_NFSD_PATH"/fs-largefile
    ./bench/run-go-nfsd.sh -disk "" "$GO_NFSD_PATH"/bench/app-bench.sh "$XV6_PATH" /mnt/nfs

    echo 1>&2
    info "Linux ext4 over NFS"
    echo "fs=linux"
    ./bench/run-linux.sh "$GO_NFSD_PATH"/fs-smallfile -start="$startthreads" -threads="$threads"
    ./bench/run-linux.sh "$GO_NFSD_PATH"/fs-largefile
    ./bench/run-linux.sh "$GO_NFSD_PATH"/bench/app-bench.sh "$XV6_PATH" /mnt/nfs
}

if [ "$output_file" = "-" ]; then
    do_eval
else
    do_eval | tee "$output_file"
fi
