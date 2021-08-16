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

type Workload struct {
	Fs    Fs
	Bench Benchmark
}

func (w Workload) Run() []Observation {
	lines := w.Fs.Run(w.Bench.Command())
	obs := w.Bench.ParseOutput(lines)
	for i := range obs {
		obs[i].Config["fs"] = w.Fs.opts
	}
	return obs
}

func (bs *BenchmarkSuite) Workloads() []Workload {
	var benches []Benchmark
	for i := 0; i < bs.Iters; i++ {
		for _, b := range bs.Benches {
			config := b.Config.Clone()
			config["meta"] = KeyValue{"iter": float64(i)}
			b := Benchmark{
				command: b.command,
				Config:  config,
				regex:   b.regex,
			}
			benches = append(benches, b)
		}
	}
	if bs.Randomize {
		rand.Shuffle(len(benches), func(i int, j int) {
			benches[i], benches[j] = benches[j], benches[i]
		})
	}
	var ws []Workload
	for _, fsOpts := range bs.Filesystems {
		fs := GetFilesys(fsOpts)
		for _, b := range benches {
			ws = append(ws, Workload{fs, b})
		}
	}
	return ws
}

func BenchSuite(smallfileDuration string) []Benchmark {
	return []Benchmark{
		LargefileBench(100),
		SmallfileBench(smallfileDuration, 1),
		AppBench(),
	}
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
			{"fs": "ext4", "mount-opts": "data=journal",
				"nfs-mount-opts": "wsize=65536,rsize=65536"},
			{"fs": "ext4", "mount-opts": "data=ordered",
				"nfs-mount-opts": "wsize=65536,rsize=65536"},
			{"fs": "ext4", "mount-opts": "data=ordered",
				"nfs-mount-opts": "wsize=65536,rsize=65536,sync"},
			{"fs": "btrfs", "mount-opts": "",
				"nfs-mount-opts": "wsize=65536,rsize=65536"},
			{"fs": "btrfs", "mount-opts": "flushoncommit",
				"nfs-mount-opts": "wsize=65536,rsize=65536"},
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
	kvs = extendAll(KeyValue{"nfs-mount-opts": "wsize=65536,rsize=65536"}, kvs)
	kvs = append(kvs,
		LinuxDurabilityFilesystems(disk)...)
	return extendAll(KeyValue{"size": float64(500)}, kvs)
}
