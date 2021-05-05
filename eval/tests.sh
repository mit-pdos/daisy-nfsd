#!/usr/bin/env bash

set -eu

# Run Linux kernel file-system tests.
#
# Usage: ./tests.sh <scale>
#
# scale is a factor to multiply the number of operations by. The defaults are
# chosen so that scale=1 (the default) takes roughly 10s for each test suite.

blue=$(tput setaf 4)
red=$(tput setaf 1)
reset=$(tput sgr0)

info() {
  echo -e "${blue}$1${reset}" 1>&2
}
error() {
  echo -e "${red}$1${reset}" 1>&2
}

if [ -z "${LTP_PATH:-}" ]; then
    error "\$LTP_PATH not set"
    echo "You may need to clone https://github.com/linux-test-project/ltp" 1>&2
    exit 1
fi

fs_path="$LTP_PATH"/testcases/kernel/fs

if [ ! -f "$fs_path/fsx-linux/fsx-linux" ]; then
    info "ltp tests not compiled."
    info "Run the following under $LTP_PATH:"
    cat >&2 <<EOF
    make autotools
    ./configure
    make -C testcases/kernel/fs/fsstress
    make -C testcases/kernel/fs/fsx-linux
EOF
    exit 1
fi

scale=1
if [ $# -ge 1 ]; then
  scale="$1"
fi

cd "$DAFNY_NFSD_PATH"

# from fsstress -H:
#
#   -d dir           specifies the base directory for operations
#   -f op_name=freq  changes the frequency of option name to freq
#                    the valid operation names are:
#                        chown creat dread dwrite fdatasync fsync getdents
#                        link mkdir mknod read readlink rename rmdir stat
#                        symlink sync truncate unlink write
#   -l loops         specifies the no. of times the testrun should loop.
#                     *use 0 for infinite (default 1)
#   -n nops          specifies the no. of operations per process (default 1)
#   -p nproc         specifies the no. of processes (default 1)
#   -S               prints the table of operations (omitting zero frequency)
#
# we skip symlink and mknod since they aren't supported
./bench/run-dafny-nfs.sh "$LTP_PATH"/testcases/kernel/fs/fsstress/fsstress \
    -l $((scale * 75)) -n 100 -p 4 -f symlink=0 -f mknod=0 -S -d /mnt/nfs

# from fsx-linux help:
#
# -l flen: the upper bound on file size (default 262144)
# -N numops: total # operations to do (default infinity)
#
# disable mapped operations since they don't test the server any more than
# direct reads/writes
./bench/run-dafny-nfs.sh "$LTP_PATH"/testcases/kernel/fs/fsx-linux/fsx-linux \
    -N $((scale * 20000)) -l 1000000 /mnt/nfs/x
