#!/usr/bin/env bash
set -eu

# run the entire eval

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
cd "$DIR/.."

iters=1
if [ "$#" -gt 0 ]; then
    iters="$1"
fi

#./loc.py      | tee data/lines-of-code.txt
go run ./cmd/daisy-eval -filesystems basic -dir eval/data -iters "$iters" bench
go run ./cmd/daisy-eval -filesystems basic -dir eval/data -iters "$iters" scale
./eval/plot.sh
