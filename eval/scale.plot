#!/bin/bash

set -eu

output=fig/scale.pdf
input=data/

usage() {
    echo "Usage: $0 [--input INPUT] [--output OUTPUT]" 1>&2
    echo "defaults to plotting from data/*.data" 1>&2
}

while [[ "$#" -gt 0 ]]; do
    case "$1" in
        -i | --input)
            shift
            input="$1"
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
set terminal pdf dashed noenhanced size 3.5in,2.0in
set output "${output}"

set auto x
set yrange [0:*]
set xtics 4
set ylabel "files / sec"
set format y '%.1s%c'
set xlabel "\# clients"
set key top left

set style data line

set style line 81 lt 0  # dashed
set style line 81 lt rgb "#808080"  # grey
set grid back linestyle 81

set border 3 back linestyle 80
set style line 1 lt rgb "#00A000" lw 2 pt 6
set style line 2 lt rgb "#5060D0" lw 2 pt 1
set style line 3 lt rgb "#A00000" lw 2 pt 2
set style line 4 lt rgb "#F25900" lw 2 pt 9

plot \
  "${input}/daisy-nfsd.data" using 1:(\$2) with linespoints ls 1 title 'DaisyNFS', \
  "${input}/go-nfsd.data" using 1:(\$2) with linespoints ls 2 title 'GoNFS', \
  "${input}/linux.data" using 1:(\$2) with linespoints ls 3 title 'Linux NFS'

EOF
