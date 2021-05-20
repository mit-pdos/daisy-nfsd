#!/bin/bash

#
# Usage:  ./run-daisy-nfsd.sh  go run ./cmd/fs-smallfile
#

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
# root of repo
cd "$DIR"/..

disk_file=/dev/shm/nfs.img
size_mb=400
cpu_list=""
nfs_mount_path="/mnt/nfs"
extra_args=()
while true; do
    case "$1" in
    -disk)
        shift
        disk_file="$1"
        shift
        ;;
    -size)
        shift
        size_mb="$1"
        shift
        ;;
    -mount-path)
        shift
        nfs_mount_path="$1"
        extra_args+=("-mount-path" "$nfs_mount_path")
        shift
        ;;
    --cpu-list)
        shift
        cpu_list="$1"
        shift
        ;;
    # some argument in -foo=value syntax
    -*=*)
        extra_args+=("$1")
        shift
        ;;
    -*)
        extra_args+=("$1" "$2")
        shift
        shift
        ;;
    *)
        break
        ;;
    esac
done

set -eu

if [ -z "$cpu_list" ]; then
    ./bench/start-daisy-nfsd.sh -disk "$disk_file" -size "$size_mb" "${extra_args[@]}" || exit 1
else
    taskset --cpu-list "$cpu_list" ./bench/start-daisy-nfsd.sh -size "$size_mb" -disk "$disk_file" "${extra_args[@]}" || exit 1
fi

function cleanup {
    ./bench/stop-daisy-nfsd.sh "$nfs_mount_path"
    # only delete regular files
    if [ -f "$disk_file" ]; then
        rm -f "$disk_file"
    fi
}
trap cleanup EXIT

# taskset 0x3 $1 /mnt/nfs
echo "# daisy-nfsd -disk $disk_file ${extra_args[*]}" 1>&2
echo "run $*" 1>&2
"$@"
