#!/usr/bin/env bash

set -eu

VM="dafny-vm"
if [ $# -ge 1 ]; then
  VM="$1"
fi

multipass start "$VM"
sleep 3
multipass exec "$VM" -- git -C dafny-nfsd pull
multipass exec "$VM" -- git -C dafny-nfsd gc
multipass exec "$VM" -- ./dafny-nfsd/artifact/vm-setup.sh
multipass stop "$VM"
sleep 3

set +e

# if setup already exists, replace it
if sudo VBoxManage snapshot "$VM" list | grep -q 'Setup'; then
  sudo VBoxManage snapshot "$VM" edit "Setup" --name "old Setup"
  sudo VBoxManage snapshot "$VM" take "Setup"
  sudo VBoxManage snapshot "$VM" delete "old Setup"
else
  sudo VBoxManage snapshot "$VM" take "Setup"
fi
sleep 1
