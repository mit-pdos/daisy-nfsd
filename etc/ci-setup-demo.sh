#!/usr/bin/env bash
set -eu

# make xv6 available
git clone https://github.com/mit-pdos/xv6-public ~/xv6
echo "XV6_PATH=$HOME/xv6" >> "$GITHUB_ENV"

# install exa manually
wget -O /tmp/exa.zip https://github.com/ogham/exa/releases/download/v0.10.1/exa-linux-x86_64-v0.10.1.zip
unzip -d exa-release /tmp/exa.zip
rm /tmp/exa.zip
echo "$HOME/exa-release/bin" >> "$GITHUB_PATH"

# install starship manually (with some tweaks to install command to make
# unattended)
curl -fsSL https://starship.rs/install.sh | sudo sh -s -- --yes
