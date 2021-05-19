#!/usr/bin/env bash

set -e

sudo launchctl start com.apple.rpcbind
sudo launchctl start com.apple.lockd

mkdir /tmp/nfs
