#!/bin/sh

#
# Usage:  ./stop-daisy-nfsd.sh
#

path="$1"
if [ -z "$path" ]; then
	path=/mnt/nfs
fi

killall -s SIGINT daisy-nfsd
sudo umount -f "$path"
