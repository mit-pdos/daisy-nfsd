#!/usr/bin/env bash

# Set up an Ubuntu VM with dependencies to run the evaluation.
#
# Best to run on Ubuntu at least 21.04 to have kernel patch
#

set -eu

cd

set DEBIAN_FRONTEND=noninteractive

# Install really basic dependencies

sudo apt-get update
sudo apt-get upgrade -y
sudo apt-get install -y git python3-pip wget unzip

# AWS dependencies
sudo apt-get install -y linux-tools-common linux-tools-aws stress
sudo apt-get install -y cpufrequtils

# Get source code

git clone https://github.com/mit-pdos/daisy-nfsd
ln -s ~/daisy-nfsd/eval ~/artifact

mkdir ~/code
cd ~/code
git clone https://github.com/mit-pdos/go-nfsd &
git clone https://github.com/mit-pdos/go-journal &
git clone https://github.com/mit-pdos/xv6-public &
git clone https://github.com/mit-pdos/fscq &
git clone --depth=1 https://github.com/linux-test-project/ltp &
wait
cd

cat >>~/.profile <<EOF
export DAISY_NFSD_PATH=$HOME/daisy-nfsd
export GO_NFSD_PATH=$HOME/code/go-nfsd
export GO_JRNL_PATH=$HOME/code/go-journal
export GO_JOURNAL_PATH=$HOME/code/go-journal
export PERENNIAL_PATH=$HOME/perennial
export XV6_PATH=$HOME/code/xv6-public
export FSCQ_PATH=$HOME/fscq
export LTP_PATH=$HOME/code/ltp
EOF
echo "source ~/.profile" >>~/.zshrc

# Install Dafny

DAFNY_VERSION=3.4.2
wget -O /tmp/dafny.zip "https://github.com/dafny-lang/dafny/releases/download/v$DAFNY_VERSION/dafny-$DAFNY_VERSION-x64-ubuntu-16.04.zip"
cd
unzip /tmp/dafny.zip
mv dafny .dafny-bin
rm /tmp/dafny.zip
echo "export PATH=\$HOME/.dafny-bin:\$PATH" >>~/.profile

# Set up NFS client and server

sudo apt-get install -y rpcbind nfs-common nfs-server
sudo mkdir -p /srv/nfs/bench
sudo chown "$USER:$USER" /srv/nfs/bench
sudo mkdir -p /mnt/nfs
sudo chown "$USER:$USER" /mnt/nfs
echo "/srv/nfs/bench localhost(rw,sync,no_subtree_check)" | sudo tee -a /etc/exports

## for simplicity we enable these services so they are automatically started,
## but they can instead be started manually on each boot
sudo systemctl enable rpcbind
sudo systemctl enable rpc-statd
sudo systemctl disable nfs-server
# can't run goose-nfsd and Linux NFS server at the same time
sudo systemctl stop nfs-server

# Make an nfs thread per core
sudo sed -i "s/RPCNFSDCOUNT=8/RPCNFSDCOUNT=$(nproc)/" /etc/default/nfs-kernel-server

# Set up Linux file-system tests

sudo apt-get install -y autoconf m4 automake pkg-config
cd ~/code/ltp
make -j4 autotools
./configure
make -j4 -C testcases/kernel/fs/fsstress
make -j4 -C testcases/kernel/fs/fsx-linux
cd

# Install Coq (to build FSCQ)

# opam dependencies
sudo apt-get install -y m4 bubblewrap
# coq dependencies
sudo apt-get install -y libgmp-dev

# use binary installer for opam since it has fewer dependencies than Ubuntu
# package
wget https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh
# echo is to answer question about where to install opam
echo "" | sh install.sh --no-backup
rm install.sh

opam init --auto-setup --bare
# takes ~5 minutes (compiles OCaml)
opam switch create 4.12.0+flambda --package=ocaml-variants.4.12.0+options,ocaml-option-flambda

# shellcheck disable=2046
eval $(opam env)

# takes ~5 minutes
# Coq 8.13.2 is required to build FSCQ
opam install -y -j4 coq.8.13.2

# Install FSCQ

sudo apt-get install -y ghc cabal-install libfuse-dev
cabal update
cabal install --lib rdtsc digest
cd ~/code/fscq/src
# takes ~3 minutes
make J=4 mkfs fscq
cd

# Install Python dependencies

pip3 install argparse

# Install Go and Go dependencies

GO_FILE=go1.18.linux-amd64.tar.gz
wget https://go.dev/dl/$GO_FILE
sudo rm -rf /usr/local/go && sudo tar -C /usr/local -xzf $GO_FILE
rm $GO_FILE
# shellcheck disable=SC2016
echo 'export PATH=$HOME/go/bin:/usr/local/go/bin:$PATH' >>~/.profile
export PATH=/usr/local/go/bin:$PATH
go install golang.org/x/tools/cmd/goimports@latest

cd ~/code/go-nfsd
# fetch dependencies
go build ./cmd/go-nfsd && rm go-nfsd
cd

cd ~/code
FB_FILE=filebench-1.5-alpha3.tar.gz
FB_FILE_DIR=filebench-1.5-alpha3

sudo apt-get install -y flex byacc
wget https://github.com/filebench/filebench/releases/download/1.5-alpha3/$FB_FILE
tar -xvzf $FB_FILE
cd $FB_FILE_DIR
./configure
make -j4
sudo make install

# Filebench wants ASLR disabled
echo 0 | sudo tee /proc/sys/kernel/randomize_va_space

cd ~/
sudo apt-get install ripgrep
sudo apt-get install fd-find

HYPERFINE_VERSION=1.13.0
wget https://github.com/sharkdp/hyperfine/releases/download/v${HYPERFINE_VERSION}/hyperfine_${HYPERFINE_VERSION}_amd64.deb
sudo dpkg -i hyperfine_${HYPERFINE_VERSION}_amd64.deb

#cd ~/code
#git clone https://github.com/torvalds/linux.git

git config --global pull.ff only

sudo apt-get clean
