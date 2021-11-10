#!/bin/bash

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"

input="data"

usage() {
    echo "Usage: $0 --input DIR" 1>&2
}

while [[ "$#" -gt 0 ]]; do
    case "$1" in
        -i | --input)
            shift
            input="$1"
            shift
            ;;
        -h | -help | --help)
            usage
            exit 0
            ;;
        *)
            echo "unknown option $1" 1>&2
            usage
            exit 1
            ;;
    esac
done

"$DIR/eval-patch.py" -i "$input" &&
    "$DIR/patch.plot" -i "$input" -o "$input"/patch.pdf &
"$DIR/eval.py" -i "$input" bench &&
    "$DIR/bench.plot" -i "$input" -o "$input"/bench.pdf &
if [[ -f "$input/scale.json" ]]
then
    "$DIR/eval.py" -i "$input" scale &&
        "$DIR/scale.plot" -i "$input" -o "$input"/scale.pdf &
fi
wait
