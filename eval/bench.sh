#!/bin/bash

# Extra DafnyNFSD/GooseNFSD commit combinations can be tried by passing extra
# arguments after the first.  For example,
#
# > ./bench.sh 1 abc123,xyz456 def123,master
#
# Will, in addition to the standard battery of tests, also run DafnyNFSD with
# commit abc123 using GoJournal from goose-nfsd with commit xyz456 and
# DafnyNFSD with commit def123 and goose-nfsd master.

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

shift

cd "$GOOSE_NFSD_PATH"
go build ./cmd/fs-smallfile
go build ./cmd/fs-largefile

if [[ $# -gt 0 ]]; then
for var in "$@"
do
    echo 1>&2
    IFS="," read -r dnfsver goosever <<< "$var"

    info "DafnyNFS-$dnfsver-$goosever"
    info "Assuming DafnyNFS is using $GOOSE_NFSD_PATH for GoJournal"
    cd "$GOOSE_NFSD_PATH"
    git checkout "$goosever" --quiet
    go build ./cmd/goose-nfsd && rm goose-nfsd

    cd "$DAFNY_NFSD_PATH"
    git checkout "$dnfsver" --quiet
    go mod edit -replace github.com/mit-pdos/goose-nfsd@latest="$GOOSE_NFSD_PATH"
    go mod tidy
    echo "fs=dfns-$dnfsver-$goosever"
    ./bench/run-dafny-nfs.sh "$GOOSE_NFSD_PATH"/fs-smallfile -start="$startthreads" -threads="$threads"
    ./bench/run-dafny-nfs.sh "$GOOSE_NFSD_PATH"/fs-largefile
    ./bench/run-dafny-nfs.sh "$GOOSE_NFSD_PATH"/bench/app-bench.sh "$XV6_PATH" /mnt/nfs
done

cd "$DAFNY_NFSD_PATH"
git restore .
git checkout main --quiet
cd "$GOOSE_NFSD_PATH"
git checkout master --quiet
go build ./cmd/goose-nfsd && rm goose-nfsd
fi


cd "$DAFNY_NFSD_PATH"

echo 1>&2
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
