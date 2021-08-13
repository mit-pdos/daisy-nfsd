#!/bin/bash

set -eu

output=fig/bench.pdf
input=data/bench.data

usage() {
    echo "Usage: $0 [--input INPUT] [--output OUTPUT]" 1>&2
    echo "defaults to plotting from data/" 1>&2
}

while [[ "$#" -gt 0 ]]; do
    case "$1" in
        -i | --input)
            shift
            input="$1"
            if [ -d "$input" ]; then
                input="$input/bench.data"
            fi
            shift
            ;;
        -o | --output)
            shift
            output="$1"
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

gnuplot <<-EOF
set terminal pdf dashed noenhanced size 3.5in,1.5in
set output "${output}"

set style data histogram
set style histogram cluster gap 1
set rmargin at screen .95

set xrange [-1:4.5]
set yrange [0:*]
set grid y
set ylabel "Relative throughput"
set ytics scale 0.5,0 nomirror
set xtics scale 0,0
set key top right
set style fill solid 1 border rgb "black"

set label 'file/s' at (0.15 -4./7),1 right rotate by 90 offset character 0,0
set label 'MB/s' at (1.15 -4./7),1 right rotate by 90 offset character 0,0
set label 'app/s' at (2.15 -4./7),1 right rotate by 90 offset character 0,0

plot "${input}" \
        using (\$2/\$2):xtic(1) title col lc rgb '#b6d7a8' lt 1, \
     '' using (\$3/\$2):xtic(1) title col lc rgb '#3a81ba' lt 1, \
     '' using (\$4/\$2):xtic(1) title col lc rgb '#cc0000' lt 1, \

EOF
