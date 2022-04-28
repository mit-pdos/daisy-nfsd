#!/usr/bin/env bash

set -eu

# Set up DaisyNFS to use a patch on go-journal
#
# Assumes the environment variables for the eval have been setup (eg,
# GO_JOURNAL_PATH).

usage() {
    echo "Usage: $0 (--undo | PATCH_FILE)" 2>&1
}

undo=false
while [[ $# -gt 0 ]]; do
    case "$1" in
    -undo | --undo)
        shift
        undo=true
        ;;
    -help | --help)
        usage
        exit 0
        ;;
    -*)
        usage
        exit 1
        ;;
    *)
        break
        ;;
    esac
done

if [ "$undo" = "true" ]; then
    cd "$GO_JOURNAL_PATH"
    git restore .
    cd "$DAISY_NFSD_PATH"
    go mod edit -dropreplace github.com/mit-pdos/go-journal
    exit 0
fi

if [[ $# -eq 0 ]]; then
    echo "Missing patch file" 1>&2
    usage
    exit 1
fi

patch_file=$(realpath "$1")

cd "$GO_JOURNAL_PATH"
if ! git diff --quiet --exit-code; then
    echo "go-journal repo is dirty, not applying patch" 1>&2
    exit 1
fi
git apply "$patch_file"

cd "$DAISY_NFSD_PATH"
go mod edit -replace github.com/mit-pdos/go-journal="$GO_JOURNAL_PATH"
