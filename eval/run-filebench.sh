threads=10
if [[ $# -gt 0 ]]; then
    threads="$1"
fi
time=10

cp /usr/local/share/filebench/workloads/$2 /tmp/$2
sed -i "s|dir=.*|dir=/mnt/nfs|" /tmp/$2

for i in `seq 1 $threads`;
do
    sed -i "s/nthreads=[0-9]*/nthreads=$i/" /tmp/$2
    sed -i "s/run [0-9]*/run $time/" /tmp/$2
    ops=$(sudo filebench -f /tmp/$2 | grep "Summary" | cut -d " " -f6-7)
    echo $2: $i $ops
done
