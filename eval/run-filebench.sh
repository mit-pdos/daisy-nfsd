#!/bin/bash

set -eu

threads=10
if [[ $# -gt 0 ]]; then
    threads="$1"
fi
workload="$2"
time=10

cp /usr/local/share/filebench/workloads/"$workload" /tmp/"$workload"
sed -i "s|dir=.*|dir=/mnt/nfs|" /tmp/"$workload"

for i in $(seq 1 "$threads");
do
    sed -i "s/nthreads=[0-9]*/nthreads=$i/" /tmp/"$workload"
    sed -i "s/run [0-9]*/run $time/" /tmp/"$workload"
    ops=$(sudo filebench -f /tmp/"$workload" | grep "Summary" | cut -d " " -f6-7)
    echo "$workload": "$i" "$ops"
done
