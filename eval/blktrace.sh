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
