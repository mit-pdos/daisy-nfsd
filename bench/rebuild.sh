#!/usr/bin/env bash

set -eu

#
# Usage:  ./rebuild-go-nfsd.sh <arguments>
#
#

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
# root of repo
cd "$DIR"/..

jrnl_patch_path=""
proj_path="."
exec_path=""
extra_args=()
while [[ "$#" -gt 0 ]]; do
    case "$1" in
        -jrnlpatch)
            shift
            jrnl_patch_path="$1"
            shift
            ;;
        -proj)
            shift
            proj_path="$1"
            shift
            ;;
        -exec)
            shift
            exec_path="$1"
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

if [[ ! -z "$jrnl_patch_path" ]]
then
	jrnl_patch_path=$(realpath "$jrnl_patch_path")

	pushd "$GO_JRNL_PATH"
	git reset --hard
	git apply "$jrnl_patch_path"
	popd

	pushd "$DAISY_NFSD_PATH"
	go mod edit -replace github.com/mit-pdos/go-journal="$GO_JRNL_PATH"
	popd

	pushd "$GO_NFSD_PATH"
	go mod edit -replace github.com/mit-pdos/go-journal="$GO_JRNL_PATH"
	popd
fi

(cd "$proj_path" && go build "$exec_path")

if [[ ! -z "$jrnl_patch_path" ]]
then
	pushd "$GO_JRNL_PATH"
	git reset --hard
	popd

	pushd "$DAISY_NFSD_PATH"
	go mod edit -dropreplace github.com/mit-pdos/go-journal
	popd

	pushd "$GO_NFSD_PATH"
	go mod edit -dropreplace github.com/mit-pdos/go-journal
	popd
fi
