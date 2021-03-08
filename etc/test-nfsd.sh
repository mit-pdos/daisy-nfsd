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

go run ./cmd/dafny-nfsd -debug=1 || true &
NFSD_PID=$!

sleep 1 # wait for server to start up
kill -0 $NFSD_PID # make sure server is running
sudo mount localhost:/ "$path"

function cleanup {
    sudo umount -f -l "$path"
    kill $NFSD_PID
}
trap cleanup EXIT

go run ./cmd/fs-test "$path"
