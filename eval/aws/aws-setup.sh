#!/bin/bash
RPC_NFSD_COUNT=36
SSD=/dev/nvme1n1

set -eu

# set up tmux
cat >~/.tmux.conf <<EOF
# fix colors
set-option -g default-terminal "tmux-256color"
# use ctrl-space as prefix (instead of ctrl-b)
set-option -g prefix C-Space
bind-key Space send-prefix
bind-key C-Space next-window
bind-key a last-window
bind-key C-a last-window
EOF

cd "$GO_NFSD_PATH"
git pull
go build ./cmd/go-nfsd
go build ./cmd/fs-smallfile
go build ./cmd/fs-largefile

cd "$DAISY_NFSD_PATH"
git pull
make compile
go build ./cmd/daisy-nfsd
go build ./cmd/daisy-eval

# need to warmup, otherwise compilation is slow the first time
./bench/run-daisy-nfsd.sh "$GO_NFSD_PATH"/bench/app-bench.sh "$XV6_PATH" /mnt/nfs

sudo cpupower frequency-set --governor performance
# for cpu in /sys/devices/system/cpu/cpu*; do
#     echo "performance" | sudo tee "$cpu"/cpufreq/scaling_governor >/dev/null
# done

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

# disable turbo boost
sudo sh -c "echo 1 > /sys/devices/system/cpu/intel_pstate/no_turbo"

sudo sed -i "s/RPCNFSDCOUNT=[0-9]*/RPCNFSDCOUNT=$RPC_NFSD_COUNT/" /etc/default/nfs-kernel-server
grep RPCNFSDCOUNT /etc/default/nfs-kernel-server

sudo turbostat stress -c 2 -t 10 2>&1 | tee data/cpuinfo.txt

# Filebench wants ASLR disabled
echo 0 | sudo tee /proc/sys/kernel/randomize_va_space

sudo chown "$USER" "$SSD"
