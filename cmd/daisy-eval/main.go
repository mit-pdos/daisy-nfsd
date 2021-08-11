package main

import (
	"compress/gzip"
	"flag"
	"fmt"
	"io"
	"os"
	"strings"

	"github.com/mit-pdos/daisy-nfsd/eval"
)

// PrintObservations prints observations for manual inspection
func PrintObservations(obs []eval.Observation, w io.Writer) {
	for _, o := range obs {
		val := o.Values["val"].(float64)
		fmt.Fprintf(w, "%f ", val)
		kvs := o.Config.Pairs()
		for _, kv := range kvs {
			fmt.Fprintf(w, "%s=%v ", kv.Key, kv.Val)
		}
		fmt.Fprintf(w, "\n")
	}
}

// WriteObservations saves observations in JSON (possibly compressed) to a file
func WriteObservations(outFile string, obs []eval.Observation) error {
	var out io.WriteCloser
	out, err := os.Create(outFile)
	if err != nil {
		return fmt.Errorf("could not create output file %s: %v",
			outFile, err)
	}
	if strings.HasSuffix(outFile, ".gz") {
		out = gzip.NewWriter(out)
	}
	err = eval.WriteObservations(out, obs)
	if err != nil {
		return fmt.Errorf("could not write output: %v", err)
	}
	err = out.Close()
	return err
}

func main() {
	var suite eval.BenchmarkSuite

	flag.BoolVar(&suite.Randomize, "randomize", true,
		"randomize order of running benchmarks")
	flag.IntVar(&suite.Iters, "iters", 1,
		"number of iterations to run each configuration")

	var unstable bool
	flag.BoolVar(&unstable, "unstable", false,
		"use unstable writes in baseline systems")

	var outFile string
	flag.StringVar(&outFile, "out", "",
		"file to output to (use .gz extension for compression)")

	flag.Parse()

	suite.Filesystems = eval.BasicFilesystems(unstable)
	suite.Benches = eval.BenchSuite

	obs := suite.Run()
	if outFile == "" {
		PrintObservations(obs, os.Stdout)
		return
	}
	err := WriteObservations(outFile, obs)
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		os.Exit(1)
	}
}
