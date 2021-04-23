#!/bin/sh

#
# Usage:  ./stop-dafny-nfs.sh
#

killall -s SIGINT dafny-nfsd
sudo umount -f /mnt/nfs
