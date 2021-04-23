#!/usr/bin/env bash

set -eu

VM=dafny-vm
if [ $# -ge 1 ]; then
  VM="$1"
fi

# cache password
sudo true
multipass launch --name "$VM" --disk 20G --mem 6G --cpus 4 lts
sudo VBoxManage controlvm "$VM" natpf1 "host-ssh,tcp,,10422,,22"
multipass exec "$VM" -- sudo apt-get -y update
multipass exec "$VM" -- sudo apt-get -y upgrade
multipass exec "$VM" -- sudo apt-get -y install zsh
multipass exec "$VM" -- wget https://raw.githubusercontent.com/ohmyzsh/ohmyzsh/master/tools/install.sh
multipass exec "$VM" -- sh install.sh --unattended
multipass exec "$VM" -- rm install.sh
multipass exec "$VM" -- sudo chsh -s /usr/bin/zsh ubuntu
multipass exec "$VM" -- sudo passwd -d ubuntu
multipass exec "$VM" -- sudo sed -e 's/#PermitEmptyPasswords no/PermitEmptyPasswords yes/' -i /etc/ssh/sshd_config
multipass exec "$VM" -- git clone https://github.com/mit-pdos/dafny-nfsd
multipass exec "$VM" --
multipass stop dafny-vm
sudo VBoxManage snapshot "$VM" take "Install"
