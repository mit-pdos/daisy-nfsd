package eval

import (
	"math/rand"
)

type BenchmarkSuite struct {
	Iters       int
	Randomize   bool
	Filesystems []KeyValue
	Benches     func() []Benchmark
}

func (bs *BenchmarkSuite) Run() []Observation {
	var benches []Benchmark
	for i := 0; i < bs.Iters; i++ {
		for _, b := range bs.Benches() {
			b.Config["meta"] = KeyValue{"iter": float64(i)}
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
			for i := range newObs {
				newObs[i].Config["meta"].(KeyValue)["iters"] = float64(bs.Iters)
			}
			obs = append(obs, newObs...)
		}
	}
	return obs
}

func BenchSuite() []Benchmark {
	return []Benchmark{
		LargefileBench(100),
		SmallfileBench("20s", 10),
		AppBench(),
	}
}

func LargefileSuite() []Benchmark {
	return []Benchmark{
		LargefileBench(100),
	}
}

func ScaleSuite(threads int) func() []Benchmark {
	return func() []Benchmark {
		var bs []Benchmark
		for i := 0; i < threads; i++ {
			bs = append(bs, SmallfileBench("10s", i))
		}
		return bs
	}
}

func BasicFilesystems(unstable bool) []KeyValue {
	ext4Opts := "data=journal"
	if unstable {
		ext4Opts = "data=ordered"
	}
	return []KeyValue{
		{
			"name":           "daisy-nfsd",
			"disk":           "", // in-memory
			"size":           float64(500),
			"nfs-mount-opts": "wsize=65536,rsize=65536",
		},
		{
			"name":           "linux",
			"fs":             "ext4",
			"disk":           "/dev/shm/disk.img",
			"size":           float64(500),
			"mount-opts":     ext4Opts,
			"nfs-mount-opts": "wsize=65536,rsize=65536",
		},
		{
			"name":           "go-nfsd",
			"unstable":       unstable,
			"disk":           "", // in-memory
			"size":           float64(500),
			"nfs-mount-opts": "wsize=65536,rsize=65536",
		},
	}
}
