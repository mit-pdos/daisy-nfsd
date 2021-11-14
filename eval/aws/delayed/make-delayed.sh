#!/bin/bash
set -eu

size=$(blockdev --getsize $1) # Size in 512-bytes sectors
echo "0 $size delay $1 0 2 $1 0 2" | dmsetup create delayed
