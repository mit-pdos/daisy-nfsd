#!/usr/bin/env bash

set -eu

#
# Usage:  ./run-txn-bench.sh <arguments>
#

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
# root of repo
cd "$DIR"/..

benchtime=""
threads=""
disk=""
jrnl_patch_path=""
extra_args=()
while [[ "$#" -gt 0 ]]; do
    case "$1" in
        -jrnlpatch=*)
            jrnl_patch_path="${1#*=}"
            shift
            ;;
        -benchtime=*)
            benchtime="${1#*=}"
            shift
            ;;
        -threads=*)
            threads="${1#*=}"
            shift
            ;;
        -disk=*)
            disk="${1#*=}"
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

./bench/rebuild.sh -jrnlpatch "$jrnl_patch_path" -proj ${GO_NFSD_PATH} -exec ./cmd/txn-bench
"${GO_NFSD_PATH}/txn-bench" --benchtime "$benchtime" --threads "$threads" --disk "$disk"
