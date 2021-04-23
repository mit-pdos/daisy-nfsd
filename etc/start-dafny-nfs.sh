#!/bin/bash

set -eu

#
# Usage:  ./start-dafny-nfs.sh <arguments>
#
# default disk is /dev/shm/dafny.img but can be overriden by passing -disk again
#

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# root of repo
cd $DIR/..

# make sure code is compiled in case it takes longer than 2s to build
go build ./cmd/dafny-nfsd && rm -f dafny-nfsd
go run ./cmd/dafny-nfsd/ -debug=1 -disk /dev/shm/dafny.img "$@" > nfs.out 2>&1 &
sleep 2
killall -0 dafny-nfsd # make sure server is running
sudo mount -t nfs -o vers=3 localhost:/ /mnt/nfs
