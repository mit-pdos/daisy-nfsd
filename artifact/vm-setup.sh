#!/usr/bin/env bash

# Set up an Ubuntu VM with dependencies to run the evaluation.
#
# Run this in the VM. Requires no setup after installing Ubuntu.

set -eu

cd

# Install really basic dependencies

sudo apt-get update
sudo apt-get install -y git python3-pip wget unzip

# SSH with empty password
sudo passwd -d ubuntu
sudo sed -e 's/#PermitEmptyPasswords no/PermitEmptyPasswords yes/' -i /etc/ssh/sshd_config
sudo sed -e 's/PasswordAuthentication no/PasswordAuthentication yes/' -i /etc/ssh/sshd_config
sudo systemctl restart sshd

# Get source code

## assumes https://github.com/mit-pdos/dafny-nfsd has already been cloned to
## ~/dafny-nfsd (since this is the easiest way to run this script)
ln -s ~/dafny-nfsd/artifact ~/artifact

git clone \
    --recurse-submodules \
    https://github.com/mit-pdos/perennial

mkdir ~/code
cd ~/code
git clone https://github.com/mit-pdos/goose-nfsd
git clone https://github.com/mit-pdos/xv6-public
git clone --depth=1 https://github.com/linux-test-project/ltp
cd

cat >> ~/.profile <<EOF
export DAFNY_NFSD_PATH=$HOME/dafny-nfsd
export GOOSE_NFSD_PATH=$HOME/code/goose-nfsd
export PERENNIAL_PATH=$HOME/perennial
export XV6_PATH=$HOME/code/xv6-public
export LTP_PATH=$HOME/code/ltp
EOF
echo "source ~/.profile" >> ~/.zshrc

# Install Dafny

## install dotnet with snap
sudo apt-get install -y snap
sudo snap install dotnet-sdk --classic --channel=5.0
sudo snap alias dotnet-sdk.dotnet dotnet

DAFNY_VERSION=3.1.0
wget -O /tmp/dafny.zip https://github.com/dafny-lang/dafny/releases/download/v$DAFNY_VERSION/dafny-$DAFNY_VERSION-x64-ubuntu-16.04.zip
cd
unzip /tmp/dafny.zip
rm /tmp/dafny.zip
echo "export PATH=\$HOME/dafny:\$PATH" >> ~/.profile

# Set up NFS client and server

sudo apt-get install -y rpcbind nfs-common nfs-server
sudo mkdir -p /srv/nfs/bench
sudo chown $USER:$USER /srv/nfs/bench
sudo mkdir -p /mnt/nfs
sudo chown $USER:$USER /mnt/nfs
echo "/srv/nfs/bench localhost(rw,sync,no_subtree_check)" | sudo tee -a /etc/exports

## for simplicity we enable these services so they are automatically started,
## but they can instead be started manually on each boot
sudo systemctl enable rpcbind
sudo systemctl enable rpc-statd
sudo systemctl disable nfs-server
# can't run goose-nfsd and Linux NFS server at the same time
sudo systemctl stop nfs-server

# Set up Linux file-system tests

sudo apt-get install -y autoconf m4 automake pkg-config
cd ~/code/ltp
make autotools
./configure
make -C testcases/kernel/fs/fsstress
make -C testcases/kernel/fs/fsx-linux
cd

# Install Python dependencies

pip3 install argparse pandas

# gnuplot (for creating graphs)

sudo apt-get install -y gnuplot-nox

# Install Go and Go dependencies

GO_FILE=go1.16.3.linux-amd64.tar.gz
wget https://golang.org/dl/$GO_FILE
sudo rm -rf /usr/local/go && sudo tar -C /usr/local -xzf $GO_FILE
rm $GO_FILE
echo 'export PATH=$HOME/go/bin:/usr/local/go/bin:$PATH' >> ~/.profile
export PATH=/usr/local/go/bin:$PATH
go install golang.org/x/tools/cmd/goimports@latest

cd ~/code/goose-nfsd
# fetch dependencies
go build ./cmd/goose-nfsd && rm goose-nfsd
cd

# Install Coq

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
# TODO: temporarily disabled since this takes forever
#opam switch create 4.11.0+flambda
#eval $(opam env)
#opam install -y -j4 coq.8.13.1

sudo apt clean
opam clean
