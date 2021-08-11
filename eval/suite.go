package eval

import (
	"math/rand"
)

type BenchmarkSuite struct {
	iters       int
	randomize   bool
	filesystems []KeyValue
	benches     func() []Benchmark
}

func (bs *BenchmarkSuite) Run() []Observation {
	var benches []Benchmark
	for i := 0; i < bs.iters; i++ {
		benches := bs.benches()
		for _, b := range benches {
			b.SetOpt("bench/iter", float64(i))
			benches = append(benches, b)
		}
	}
	if bs.randomize {
		rand.Shuffle(len(benches), func(i int, j int) {
			benches[i], benches[j] = benches[j], benches[i]
		})
	}
	obs := make([]Observation, 0, len(bs.filesystems)*len(benches))
	for _, fsOpts := range bs.filesystems {
		fs := GetFilesys(fsOpts)
		for _, b := range benches {
			newObs := RunBenchmark(fs, b)
			for i := range newObs {
				newObs[i].Config["meta/iters"] = float64(bs.iters)
			}
			obs = append(obs, newObs...)
		}
	}
	return obs
}
