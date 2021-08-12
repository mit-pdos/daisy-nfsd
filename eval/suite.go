package eval

import (
	"math/rand"
)

type BenchmarkSuite struct {
	Iters       int
	Randomize   bool
	Filesystems []KeyValue
	Benches     []Benchmark
}

func (bs *BenchmarkSuite) Run() []Observation {
	var benches []Benchmark
	for i := 0; i < bs.Iters; i++ {
		for _, b := range bs.Benches {
			b := Benchmark{
				command: b.command,
				Config:  b.Config.Clone(),
				regex:   b.regex,
			}
			b.Config["meta"] = KeyValue{
				"iter":  float64(i),
				"iters": float64(bs.Iters),
			}
			benches = append(benches, b)
		}
	}
	if bs.Randomize {
		rand.Shuffle(len(benches), func(i int, j int) {
			benches[i], benches[j] = benches[j], benches[i]
		})
	}
	obs := make([]Observation, 0, len(bs.Filesystems)*len(benches))
	for _, fsOpts := range bs.Filesystems {
		fs := GetFilesys(fsOpts)
		for _, b := range benches {
			newObs := RunBenchmark(fs, b)
			obs = append(obs, newObs...)
		}
	}
	return obs
}

var BenchSuite = []Benchmark{
	LargefileBench(100),
	SmallfileBench("20s", 10),
	AppBench(),
}

var LargefileSuite = []Benchmark{
	LargefileBench(100),
}

func ScaleSuite(benchtime string, threads int) []Benchmark {
	var bs []Benchmark
	for i := 1; i <= threads; i++ {
		bs = append(bs, SmallfileBench(benchtime, i))
	}
	return bs
}

func extendAll(common KeyValue, kvs []KeyValue) []KeyValue {
	for i := range kvs {
		kvs[i].Extend(common)
	}
	return kvs
}

func BasicFilesystems(disk string, unstable bool) []KeyValue {
	nfsdDisk := disk
	linuxDisk := disk
	if disk == ":memory:" {
		nfsdDisk = "" // use MemDisk
		linuxDisk = "/dev/shm/disk.img"
	}
	ext4Opts := "data=journal"
	if unstable {
		ext4Opts = "data=ordered"
	}
	return extendAll(KeyValue{
		"size":           float64(500),
		"nfs-mount-opts": "wsize=65536,rsize=65536",
	},
		[]KeyValue{
			{
				"name": "daisy-nfsd",
				"disk": nfsdDisk,
			},
			{
				"name":       "linux",
				"fs":         "ext4",
				"disk":       linuxDisk,
				"mount-opts": ext4Opts,
			},
			{
				"name":     "go-nfsd",
				"unstable": unstable,
				"disk":     nfsdDisk,
			},
		})
}

// LinuxDurabilityFilesystems returns many Linux filesystems,
// varying durability options
func LinuxDurabilityFilesystems(disk string) []KeyValue {
	if disk == ":memory:" {
		disk = "/dev/shm/disk.img"
	}
	kvs := extendAll(KeyValue{"name": "linux", "disk": disk},
		[]KeyValue{
			{"fs": "ext4", "mount-opts": "data=journal"},
			{"fs": "ext4", "mount-opts": "data=ordered"},
			{"fs": "ext4", "mount-opts": "data=ordered",
				"nfs-mount-opts": "wsize=65536,rsize=65536,sync"},
			{"fs": "btrfs", "mount-opts": ""},
			{"fs": "btrfs", "mount-opts": "flushoncommit"},
			{"fs": "btrfs", "mount-opts": "",
				"nfs-mount-opts": "wsize=65536,rsize=65536,sync"},
		})
	return kvs
}

func ManyDurabilityFilesystems(disk string) []KeyValue {
	var kvs []KeyValue
	if disk == ":memory:" {
		kvs = append(kvs,
			extendAll(KeyValue{"name": "daisy-nfsd"},
				[]KeyValue{
					{"disk": "/dev/shm/disk.img"},
					{"disk": ""},
				})...)
	} else {
		kvs = append(kvs,
			extendAll(KeyValue{"name": "daisy-nfsd"},
				[]KeyValue{
					{"disk": disk},
				})...)
	}
	if disk == ":memory:" {
		kvs = append(kvs,
			extendAll(KeyValue{"name": "go-nfsd"},
				[]KeyValue{
					{"disk": "/dev/shm/disk.img", "unstable": true},
					{"disk": "/dev/shm/disk.img", "unstable": false},
					{"disk": "", "unstable": true},
					{"disk": "", "unstable": false},
				})...)
	} else {
		kvs = append(kvs,
			extendAll(KeyValue{"name": "go-nfsd"},
				[]KeyValue{
					{"disk": disk, "unstable": true},
					{"disk": disk, "unstable": false},
				})...)
	}
	kvs = append(kvs,
		LinuxDurabilityFilesystems(disk)...)
	return extendAll(KeyValue{"size": float64(500)}, kvs)
}
