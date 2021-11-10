package eval

import (
	"fmt"
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
		LargefileBench(300),
		SmallfileBench(smallfileDuration, 1),
		AppBench(),
	}
}

var LargefileSuite = []Benchmark{
	LargefileBench(300),
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

func BasicFilesystem(name string, disk string, unstable bool, jrnlpatch string) KeyValue {
	nfsdDisk := disk
	linuxDisk := disk
	if disk == ":memory:" {
		nfsdDisk = "" // use MemDisk
		linuxDisk = "/dev/shm/disk.img"
	}
	var config KeyValue
	switch name {
	case "daisy-nfsd":
		config = KeyValue{
			"disk": nfsdDisk,
			"jrnlpatch": jrnlpatch,
		}
	case "linux":
		opts := "data=journal"
		if unstable {
			opts = "data=ordered"
		}
		config = KeyValue{
			"fs":             "ext4",
			"disk":           linuxDisk,
			"mount-opts":     opts,
			"nfs-mount-opts": "wsize=65536,rsize=65536",
		}
	case "go-nfsd":
		config = KeyValue{
			"unstable": unstable,
			"disk":     nfsdDisk,
		}
	default:
		panic(fmt.Sprintf("invalid filesystem %s", name))
	}
	config.Extend(KeyValue{
		"name": name,
		"size": float64(800),
	})
	return config
}

// LinuxDurabilityFilesystems returns many Linux filesystems,
// varying durability options
func LinuxDurabilityFilesystems(disk string) []KeyValue {
	if disk == ":memory:" {
		disk = "/dev/shm/disk.img"
	}
	kvs := extendAll(KeyValue{"name": "linux", "disk": disk},
		// not a perfect cross product because using NFS sync means the
		// underlying file system's durability is irrelevant, so we only test
		// one configuration
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
	nfsMountOpts := []interface{}{
		// under sync the write size will be 65536=16*4k since that's the write
		// size in largefile anyway, so use the same batch size without it for a
		// fair comparison
		"wsize=65536,rsize=65536",
		"wsize=65536,rsize=65536,sync",
	}
	var kvs []KeyValue
	if disk == ":memory:" {
		kvs = append(kvs,
			KeyValue{
				"name":           "daisy-nfsd",
				"disk":           []interface{}{"/dev/shm/disk.img", ""},
				"nfs-mount-opts": nfsMountOpts,
			}.Product()...)
	} else {
		kvs = append(kvs,
			KeyValue{
				"name":           "daisy-nfsd",
				"disk":           disk,
				"nfs-mount-opts": nfsMountOpts,
			}.Product()...)
	}
	if disk == ":memory:" {
		kvs = append(kvs,
			KeyValue{
				"name":           "go-nfsd",
				"disk":           []interface{}{"/dev/shm/disk.img", ""},
				"unstable":       []interface{}{true, false},
				"nfs-mount-opts": nfsMountOpts,
			})
	} else {
		kvs = append(kvs,
			KeyValue{
				"name":           "go-nfsd",
				"disk":           disk,
				"unstable":       []interface{}{true, false},
				"nfs-mount-opts": nfsMountOpts,
			}.Product()...)
	}
	kvs = append(kvs,
		LinuxDurabilityFilesystems(disk)...)
	return extendAll(KeyValue{"size": float64(800)}, kvs)
}
