#!/usr/bin/env bash

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
    echo "Usage: $0 [--disk DISK] [-benchtime TIME] [-par PAR] [-file-size SIZE]" 1>&2
}

output_file="$DAISY_NFSD_PATH/eval/data/bench-raw.txt"
disk="/dev/nvme1n1"
# time to run smallfile
benchtime="20s"
# number of threads for smallfile-par
par=20
# largefile size (MB)
file_size=300

while [[ "$#" -gt 0 ]]; do
    case "$1" in
    -help | --help)
        usage
        exit 0
        ;;
    -o | --output)
        shift
        output_file="$1"
        shift
        ;;
    -disk)
        shift
        disk="$1"
        shift
        ;;
    -benchtime)
        shift
        benchtime="$1"
        shift
        ;;
    -par)
        shift
        par="$1"
        shift
        ;;
    -file-size)
        shift
        file_size="$1"
        shift
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

daisy() {
    ./bench/run-daisy-nfsd.sh -disk "$disk" -size 1000 "$@"
}

daisy_seq_wal() {
    daisy -patch "$GO_NFSD_PATH"/eval/serial.patch "$@"
}

daisy_seq_txn() {
    daisy -patch "$GO_NFSD_PATH"/eval/global-txn-lock.patch "$@"
}

linux() {
    $GO_NFSD_PATH/bench/run-linux.sh -disk "$disk" -size 1000 "$@"
}

do_eval() {
    info "smallfile-1"
    echo "fs=dnfs"
    daisy "$GO_NFSD_PATH"/fs-smallfile -start=1 -threads=1 -benchtime="$benchtime"

    echo "fs=dnfs-seq-wal"
    daisy_seq_wal "$GO_NFSD_PATH"/fs-smallfile -start=1 -threads=1 -benchtime="$benchtime"

    echo "fs=dnfs-seq-txn"
    daisy_seq_txn "$GO_NFSD_PATH"/fs-smallfile -start=1 -threads=1 -benchtime="$benchtime"

    echo "fs=linux"
    linux "$GO_NFSD_PATH"/fs-smallfile -start=1 -threads=1 -benchtime="$benchtime"

    echo "fs=linux-ordered"
    linux -mount-opts "data=ordered" "$GO_NFSD_PATH"/fs-smallfile -start=1 -threads=1 -benchtime="$benchtime"

    echo 1>&2
    info "smallfile-$par"
    echo "fs=dnfs"
    daisy "$GO_NFSD_PATH"/fs-smallfile -start=$par -threads=$par -benchtime="$benchtime"

    echo "fs=dnfs-seq-wal"
    daisy_seq_wal "$GO_NFSD_PATH"/fs-smallfile -start=$par -threads=$par -benchtime="$benchtime"

    echo "fs=dnfs-seq-txn"
    daisy_seq_txn "$GO_NFSD_PATH"/fs-smallfile -start=$par -threads=$par -benchtime="$benchtime"

    echo "fs=linux"
    linux "$GO_NFSD_PATH"/fs-smallfile -start=$par -threads=$par -benchtime="$benchtime"

    echo "fs=linux-ordered"
    linux -mount-opts "data=ordered" "$GO_NFSD_PATH"/fs-smallfile -start=$par -threads=$par -benchtime="$benchtime"

    echo 1>&2
    info "largefile"
    echo "fs=dnfs"
    daisy "$GO_NFSD_PATH"/fs-largefile -file-size "$file_size"

    echo "fs=dnfs-seq-wal"
    daisy_seq_wal "$GO_NFSD_PATH"/fs-largefile -file-size "$file_size"

    echo "fs=dnfs-seq-txn"
    daisy_seq_txn "$GO_NFSD_PATH"/fs-largefile -file-size "$file_size"

    echo "fs=linux"
    linux "$GO_NFSD_PATH"/fs-largefile -file-size "$file_size"

    echo "fs=linux-ordered"
    linux -mount-opts "data=ordered" "$GO_NFSD_PATH"/fs-largefile -file-size "$file_size"

    echo 1>&2
    info "app"
    echo "fs=dnfs"
    daisy "$GO_NFSD_PATH"/bench/app-bench.sh "$XV6_PATH" /mnt/nfs

    echo "fs=dnfs-seq-wal"
    daisy_seq_wal "$GO_NFSD_PATH"/bench/app-bench.sh "$XV6_PATH" /mnt/nfs

    echo "fs=dnfs-seq-txn"
    daisy_seq_txn "$GO_NFSD_PATH"/bench/app-bench.sh "$XV6_PATH" /mnt/nfs

    echo "fs=linux"
    linux "$GO_NFSD_PATH"/bench/app-bench.sh "$XV6_PATH" /mnt/nfs

    echo "fs=linux-ordered"
    linux -mount-opts "data=ordered" "$GO_NFSD_PATH"/bench/app-bench.sh "$XV6_PATH" /mnt/nfs
}

if [ "$output_file" = "-" ]; then
    do_eval
else
    do_eval | tee "$output_file"
fi
