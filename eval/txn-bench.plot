#!/bin/bash

set -eu

output=fig/patch.pdf
input=data/txn-bench.data
ssd=false

usage() {
    echo "Usage: $0 [--input INPUT] [--output OUTPUT] [-ssd]" 1>&2
    echo "defaults to plotting RAM benchmarks from data/txn-bench.data" 1>&2
}

while [[ "$#" -gt 0 ]]; do
    case "$1" in
        -i | --input)
            shift
            input="$1"
            if [ -d "$input" ]; then
                input="$input/txn-bench.data"
            fi
            shift
            ;;
        -o | --output)
            shift
            output="$1"
            shift
            ;;
        -ssd)
            ssd=true
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

label=""
line1='column("orig")/column("orig")'
line2='column("no-append-merge")/column("orig")'
line3='column("no-install-merge")/column("orig")'
line4='column("no-merge")/column("orig")'
label1=$(awk 'NR==2 {printf "%.0f", $2}' "$input")

gnuplot <<-EOF
	set terminal pdf dashed noenhanced size 11cm,9cm
	set output "${output}"

	set style data histogram
	set style histogram cluster gap 2
	set rmargin at screen .95

	set xrange [-1:4]
	set yrange [0:*]
	set grid y
	set ylabel "Relative throughput"
	set ytics scale 0.5,0 nomirror
	set xtics scale 0,0
	set key top right
	set style fill solid 1 border rgb "black"
	set offset 0, -1, 0, 0

	set label '${label1} txn/s' at (0.08 -4./7),1 right rotate by 90 offset character 0,-1

	set datafile separator "\t"

	plot "${input}" \
	        using (${line1}):xtic(1) title "orig${label}" lc rgb '#b6d7a8' lt 1, \
	     '' using (${line2}):xtic(1) title "no-merge-on-append${label}" lc rgb '#3a81ba' lt 1, \
       '' using (${line3}):xtic(1) title "no-merge-on-install${label}" lc rgb '#cc0000' lt 1, \
       '' using (${line4}):xtic(1) title "no-merge${label}" lc rgb '#00cc00' lt 1, \

EOF
