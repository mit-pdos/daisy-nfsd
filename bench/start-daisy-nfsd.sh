#!/usr/bin/env bash

set -eu

#
# Usage:  ./start-daisy-nfsd.sh <arguments>
#
# default disk is /dev/shm/nfs.img but can be overriden by passing -disk again
#

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
# root of repo
cd "$DIR"/..

disk_path=/dev/shm/nfs.img
nfs_mount_opts=""
nfs_mount_path="/mnt/nfs"
extra_args=()
size_mb=400
while [[ "$#" -gt 0 ]]; do
    case "$1" in
    -disk)
        shift
        disk_path="$1"
        shift
        ;;
    -size)
        shift
        size_mb="$1"
        shift
        ;;
    -nfs-mount-opts)
        shift
        nfs_mount_opts="$1"
        shift
        ;;
    -mount-path)
        shift
        nfs_mount_path="$1"
        shift
        ;;
    -*=*)
        extra_args+=("$1")
        shift
        ;;
    -*)
        extra_args+=("$1" "$2")
        shift
        shift
        ;;
    esac
done

make --quiet compile
go build ./cmd/daisy-nfsd
if [ -e "$disk_path" ]; then
    dd if=/dev/zero of="$disk_path" bs=4k count=$((size_mb * 1024 / 4)) 1>/dev/null 2>&1
fi
# ${a[@]+"${a[@]}"} checks if a is set and if so, expands to it as an array
# "${a[@]}" should be sufficient but this idiom is compatible with bash 3 which macOS ships with
# see https://stackoverflow.com/questions/7577052/bash-empty-array-expansion-with-set-u
./daisy-nfsd -debug=0 -disk "$disk_path" -size "$size_mb" ${extra_args[@]+"${extra_args[@]}"} 1>nfs.out 2>&1 &
sleep 2
killall -0 daisy-nfsd       # make sure server is running
killall -SIGUSR1 daisy-nfsd # reset stats after recovery

# mount options for Linux NFS client:
#
# vers=3 is the default but nice to be explicit
#
# nordirplus tells the client not to try READDIRPLUS (it will fall back to
# READDIR but always first try READDIRPLUS)
#
# nolock tells the client not to try to use the Network Lock Manager for
# advisory locks since our server doesn't run one; instead, clients use local
# locks which work fine if there's only one client
_nfs_mount="vers=3,nordirplus,nolock"
if [ -n "$nfs_mount_opts" ]; then
    _nfs_mount="vers=3,nordirplus,$nfs_mount_opts"
fi

sudo mount -t nfs -o "${_nfs_mount}" localhost:/ "$nfs_mount_path"
