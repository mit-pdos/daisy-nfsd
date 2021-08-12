package main

import (
	"compress/gzip"
	"fmt"
	"io"
	"os"
	"strings"

	"github.com/mit-pdos/daisy-nfsd/eval"
	"github.com/urfave/cli/v2"
)

// PrintObservations prints observations for manual inspection
func printObservations(w io.Writer, obs []eval.Observation) {
	for _, o := range obs {
		val := o.Values["val"].(float64)
		fmt.Fprintf(w, "%f ", val)
		for _, kv := range o.Config.Flatten().Pairs() {
			fmt.Fprintf(w, "%s=%v ", kv.Key, kv.Val)
		}
		fmt.Fprintf(w, "\n")
	}
}

var suiteFlags = []cli.Flag{
	&cli.BoolFlag{
		Name:  "randomize",
		Value: true,
		Usage: "randomize order of running benchmarks",
	},
	&cli.IntFlag{
		Name:  "iters",
		Value: 1,
		Usage: "number of iterations to run each configuration",
	},
	&cli.StringFlag{
		Name:  "disk",
		Value: ":memory:",
		Usage: "path to disk file to use for all benchmarks " +
			"(:memory: uses tmpfs or MemFs as appropriate)",
	},
	&cli.StringFlag{
		Name:  "out",
		Value: "",
		Usage: "file to output to (use .gz extension for compression)",
	},
	&cli.BoolFlag{
		Name:  "flatten",
		Value: true,
		Usage: "flatten output configurations for compatibility with pandas",
	},
}

// WriteObservations saves observations in JSON (possibly compressed) to a file
func writeObservations(outFile string, obs []eval.Observation) error {
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

// OutputObservations outputs based on flags
func OutputObservations(c *cli.Context, obs []eval.Observation) error {
	outFile := c.String("out")
	if c.Bool("flatten") {
		for i := range obs {
			obs[i].Config = obs[i].Config.Flatten()
		}
	}
	if outFile == "" {
		printObservations(os.Stdout, obs)
		return nil
	}
	return writeObservations(outFile, obs)
}

func initializeSuite(c *cli.Context) *eval.BenchmarkSuite {
	return &eval.BenchmarkSuite{
		Iters:     c.Int("iters"),
		Randomize: c.Bool("randomize"),
	}
}

func beforeBench(_ *cli.Context) error {
	eval.PrepareBenchmarks()
	return nil
}

var benchCommand = &cli.Command{
	Name:  "bench",
	Usage: "run a few single-threaded benchmarks",
	Flags: []cli.Flag{&cli.BoolFlag{
		Name:  "unstable",
		Usage: "use unstable writes in baseline systems",
	}},
	Before: beforeBench,
	Action: func(c *cli.Context) error {
		eval.PrepareBenchmarks()
		suite := initializeSuite(c)
		suite.Filesystems =
			eval.BasicFilesystems(c.String("disk"), c.Bool("unstable"))
		suite.Benches = eval.BenchSuite
		obs := suite.Run()
		err := OutputObservations(c, obs)
		return err
	},
}

var scaleCommand = &cli.Command{
	Name:  "scale",
	Usage: "benchmark smallfile with varying clients",
	Flags: []cli.Flag{&cli.IntFlag{
		Name:  "threads",
		Value: 10,
		Usage: "maximum number of threads to run till",
	}, &cli.StringFlag{
		Name:  "benchtime",
		Value: "10s",
		Usage: "duration to run each benchmark",
	}},
	Before: beforeBench,
	Action: func(c *cli.Context) error {
		suite := initializeSuite(c)
		suite.Filesystems =
			eval.BasicFilesystems(c.String("disk"), c.Bool("unstable"))
		suite.Benches = eval.ScaleSuite(c.String("benchtime"), c.Int("threads"))
		obs := suite.Run()
		err := OutputObservations(c, obs)
		return err
	},
}

var largefileCommand = &cli.Command{
	Name:   "largefile",
	Usage:  "benchmark largefile on many filesystem configurations",
	Before: beforeBench,
	Action: func(c *cli.Context) error {
		if c.String("disk") != ":memory:" {
			return fmt.Errorf("largefile doesn't support non-memory" +
				" benchmarks (yet)")
		}
		suite := initializeSuite(c)
		suite.Filesystems =
			eval.ManyMemFilesystems()
		suite.Benches = eval.LargefileSuite
		obs := suite.Run()
		err := OutputObservations(c, obs)
		return err
	},
}

func main() {
	app := &cli.App{
		Usage: "run benchmarks",
		Flags: suiteFlags,
		Commands: []*cli.Command{
			benchCommand,
			scaleCommand,
			largefileCommand,
		},
	}
	err := app.Run(os.Args)
	if err != nil {
		fmt.Fprintln(os.Stderr, err.Error())
		os.Exit(1)
	}
}
