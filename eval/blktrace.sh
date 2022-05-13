#!/bin/bash

set -eu

time=10
iters=10000

start_daisy() {
    "$DAISY_NFSD_PATH"/bench/start-daisy-nfsd.sh -disk /dev/nvme1n1
}

stop_daisy() {
    "$DAISY_NFSD_PATH"/bench/stop-daisy-nfsd.sh
}

start_linux() {
    "$GO_NFSD_PATH"/bench/start-linux.sh -disk /dev/nvme1n1
}

stop_linux() {
    "$GO_NFSD_PATH"/bench/stop-linux.sh
}

blktrace() {
    # default format is "%D %2c %8s %5T.%9t %5p %2a %3d"
    sudo blktrace -d /dev/nvme1n1 --stopwatch "$time" -o - |
        blkparse --quiet -i - |
        grep -v 'systemd-udevd'
}

smallfile() {
    $GO_NFSD_PATH/fs-smallfile -iters="$iters"
}

start_daisy
blktrace >blktrace-daisy.out &
smallfile
wait
stop_daisy

start_linux
blktrace >blktrace-linux.out &
smallfile
wait
stop_linux

# some notes on analyzing the results:
#
# the units for offset and size appear to be in 512-byte sectors (based on
# seeing a lot of writes to 0 + 8 and 8 + 8 in daisy-nfsd).
#
# total number of sectors written:
# cat blktrace-daisy.out | grep 'D  W' | grep -o '\+ [0-9]*' | awk '{sum=sum+$2} END{print sum}'
#
# divide by 8*10000 for per-iteration writes in units of 4KB blocks
#
# total number of write I/Os:
# cat blktrace-daisy.out | grep -c 'D  W'
#
# distribution of request sizes (after merging):
# cat blktrace-daisy.out | grep 'D  W' | grep -o '\+ [0-9]*' | sort | uniq -c | sort -n
#
# distribution of addresses written:
# cat blktrace-daisy.out | grep -o 'D  WS [0-9]*' | cut -d' ' -f4 | sort | uniq -c | sort -n
