LINUX=~/code/linux/
threads=10
if [[ $# -gt 0 ]]; then
    threads="$1"
fi

# DaisyNFS cannot handle directories with more than 1024 files, so delete excess files

find $LINUX -type d -printf '%p %i\n' | while read outername outerinode
do
count=$(find $outername -type d -maxdepth 1 | wc -l)
remain=$(expr 1024 - $count)
find $outername -type f -maxdepth 1 -printf '%p %i\n' | sort -n | head -n -$remain | while read name inode
do
	    find $outername -inum "$inode" -delete
	    echo "delete $name"
done
done

# DaisyNFS cannot handle symbolic links, so delete them

find $LINUX -type l -printf "%p\n" -delete

cd /mnt/nfs
cp -r $LINUX .
cd linux

hyperfine --parameter-scan num_threads 1 $threads --prepare 'sync; echo 3 | sudo tee /proc/sys/vm/drop_caches' 'fdfind -j{num_threads} "crypto" | wc -l'

hyperfine --parameter-scan num_threads 1 $threads --prepare 'sync; echo 3 | sudo tee /proc/sys/vm/drop_caches' 'rg -j{num_threads} -c PM_PARAM'
