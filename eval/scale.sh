#!/usr/bin/env bash

# Extra DaisyNFS/GoJournal commit combinations can be tried by passing extra
# arguments after the first.  For example,
#
# > ./scale.sh 1 abc123,xyz456 def123,master
#
# Will, in addition to the standard battery of tests, also run DaisyNFS with
# commit abc123 using GoJournal from go-nfsd with commit xyz456 and
# DaisyNFS with commit def123 and go-nfsd master.

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

usage() {
    echo "Usage: $0 [-disk DISK_FILE] [-o | --output OUT_FILE] [threads]" 1>&2
    echo 1>&2
    echo "threads defaults to 10" 1>&2
    echo "DISK_FILE defaults to ~/disk.img" 1>&2
}

# the path to store the disk file in (use this to run the benchmarks on a real
# drive)
disk_file="$HOME/disk.img"
output_file="$DAISY_NFSD_PATH/eval/data/scale-raw.txt"

while true; do
    case "$1" in
        -disk)
            shift
            disk_file="$1"
            shift
            ;;
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
            error "unexpected flag $1"
            usage
            exit 1
            ;;
        *)
            break
            ;;
    esac
done
output_file=$(realpath "$output_file")

threads=10
if [[ $# -gt 0 ]]; then
    threads="$1"
fi

shift

cd "$GO_NFSD_PATH"
go build ./cmd/fs-smallfile
go build ./cmd/fs-largefile

do_eval() {
    if [[ $# -gt 0 ]]; then
        for var in "$@"; do
            echo 1>&2
            IFS="," read -r dnfsver goosever <<<"$var"

            info "DaisyNFS-$dnfsver-$goosever smallfile scalability"
            info "Assuming DaisyNFS is using $GO_JRNL_PATH for GoJournal"
            cd "$GO_JRNL_PATH"
            git checkout "$goosever" --quiet

            cd "$DAISY_NFSD_PATH"
            git checkout "$dnfsver" --quiet
            go mod edit -replace github.com/mit-pdos/go-journal="$GO_JRNL_PATH"
            echo "fs=dfns-$dnfsver-$goosever"
            ./bench/run-daisy-nfsd.sh -disk "$disk_file" "$GO_NFSD_PATH"/fs-smallfile -threads="$threads"
        done

        cd "$DAISY_NFSD_PATH"
        go mod edit -dropreplace github.com/mit-pdos/go-journal
        git checkout main --quiet
        cd "$GO_JRNL_PATH"
        git checkout master --quiet
    fi

    cd "$DAISY_NFSD_PATH"
    echo 1>&2
    info "DaisyNFS smallfile scalability"
    echo "fs=dnfs"
    ./bench/run-daisy-nfsd.sh -disk "$disk_file" "$GO_NFSD_PATH"/fs-smallfile -threads="$threads"

    cd "$GO_NFSD_PATH"
    echo 1>&2
    info "Linux smallfile scalability"
    echo "fs=linux"
    ./bench/run-linux.sh -disk "$disk_file" "$GO_NFSD_PATH"/fs-smallfile -threads="$threads"

    echo 1>&2
    info "Serial DaisyNFS (holding locks)"

    # we change the local checkout of go-journal
    cd "$GO_JRNL_PATH"
    git apply "$GO_NFSD_PATH/eval/serial.patch"
    cd "$DAISY_NFSD_PATH"
    # ... and then also point go-nfsd to the local version
    go mod edit -replace github.com/mit-pdos/go-journal="$GO_JOURNAL_PATH"

    echo "fs=serial-dnfs"
    ./bench/run-daisy-nfsd.sh -disk "$disk_file" "$GO_NFSD_PATH"/fs-smallfile -threads="$threads"

    go mod edit -dropreplace github.com/mit-pdos/go-journal
    cd "$GO_JRNL_PATH"
    git restore wal/installer.go wal/logger.go wal/wal.go

    cd "$GO_NFSD_PATH"
    echo 1>&2
    info "GoNFS smallfile scalability"
    echo "fs=gonfs"
    ./bench/run-go-nfsd.sh -disk "$disk_file" "$GO_NFSD_PATH"/fs-smallfile -threads="$threads"
}

if [ "$output_file" = "-" ]; then
    do_eval "$@"
else
    do_eval "$@" | tee "$output_file"
fi
