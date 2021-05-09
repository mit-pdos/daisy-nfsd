#!/bin/bash

set -eu

#
# Usage:  ./start-dafny-nfs.sh <arguments>
#
# default disk is /dev/shm/nfs.img but can be overriden by passing -disk again
#

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# root of repo
cd $DIR/..

# make sure code is compiled in case it takes longer than 2s to build
make --quiet compile
go build ./cmd/dafny-nfsd && rm -f dafny-nfsd
go run ./cmd/dafny-nfsd/ -debug=0 -disk /dev/shm/nfs.img "$@" 1>nfs.out 2>&1 &
# don't need nfsd to be running yet; mount will retry until it can connect
sleep 0.5
killall -0 dafny-nfsd # make sure server is running

# mount options for Linux NFS client:
#
# vers=3 is the default but nice to be explicit
#
# retry=1 tries to connect for up to a minute (default is 2)
#
# nordirplus tells the client not to try READDIRPLUS (it will fall back to
# READDIR but always first try READDIRPLUS)
#
# nolock tells the client not to try to use the Network Lock Manager for
# advisory locks since our server doesn't run one; instead, clients use local
# locks which work fine if there's only one client
sudo mount -t nfs -o vers=3,retry=1,nordirplus,nolock localhost:/ /mnt/nfs
