#!/bin/bash
RPC_NFSD_COUNT=36
SSD=/dev/nvme1n1

set -eu

cd "$GO_NFSD_PATH"
git pull
go build ./cmd/go-nfsd

cd "$DAISY_NFSD_PATH"
git pull
make compile
go build ./cmd/daisy-nfsd
go build ./cmd/daisy-eval

sudo cpupower frequency-set --governor performance

# disable all but the first numa node
for node in /sys/devices/system/node/node*; do
  if [ "$(basename "$node")" = "node0" ]; then
    continue
  fi
  for cpu in "$node/cpu"[0-9]*; do
    echo 0 | sudo tee "$cpu"/online >/dev/null
  done
done

cd "$DAISY_NFSD_PATH/eval"

lscpu | tee data/lscpu.txt
cpufreq-info | tee data/cpufreq-info.txt

sudo sh -c "echo 1 > /sys/devices/system/cpu/intel_pstate/no_turbo"

sudo sed -i "s/RPCNFSDCOUNT=[0-9]*/RPCNFSDCOUNT=$RPC_NFSD_COUNT/" /etc/default/nfs-kernel-server
grep RPCNFSDCOUNT /etc/default/nfs-kernel-server

sudo turbostat stress -c 2 -t 10 2>&1 | tee data/cpuinfo.txt

sudo chown "$USER" "$SSD"
