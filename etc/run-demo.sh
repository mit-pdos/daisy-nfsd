#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# go to project root
cd "$DIR"/..

# this script needs XV6_PATH set
if [ ! -d "$XV6_PATH" ]; then
    echo "set XV6_PATH to a checkout of https://github.com/mit-pdos/xv6-public" >&2
    exit 1
fi

set -u

# force color output that matches gold output
export TERM=xterm-256color

./bench/run-dafny-nfs.sh ./tests/demo.sh /mnt/nfs |
    sed -E 's/20[0-9]{2}-[0-9]{2}-[0-9]{2} [0-9]{2}:[0-9]{2}/2021-05-07 17:53/' |
    tee tests/demo-actual.out
diff tests/demo-expected.out tests/demo-actual.out
# if files differ diff will return a non-zero code and the script will fail

rm tests/demo-actual.out
