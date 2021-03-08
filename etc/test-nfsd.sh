#!/usr/bin/env bash
set -eu

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# root of repo
cd $DIR/..

path="$1"
if [ -z "$path" ]; then
    echo "Usage: $0 <mount path>" >&2
    exit 1
fi

sudo mount localhost:/ "$path"
go run ./cmd/dafny-nfsd -debug=1 || true &
NFSD_PID=$!

function cleanup {
    sudo umount -f -l "$path"
    kill $NFSD_PID
}
trap cleanup EXIT

sleep 1
go run ./cmd/fs-test "$path"
