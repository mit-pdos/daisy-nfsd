#!/usr/bin/env bash

set -e

sudo launchctl start com.apple.rpcbind

mkdir /tmp/nfs
