#!/bin/sh

#
# Usage:  ./stop-dafny-nfs.sh
#

path="$1"
if [ -z "$path" ]; then
	path=/mnt/nfs
fi

killall -s SIGINT dafny-nfsd
sudo umount -f "$path"
