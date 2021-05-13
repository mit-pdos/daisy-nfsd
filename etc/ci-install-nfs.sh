#!/usr/bin/env bash
set -eu

sudo apt-get -y install rpcbind nfs-common
sudo systemctl start rpcbind
sudo mkdir /mnt/nfs
sudo chown "$USER" /mnt/nfs
