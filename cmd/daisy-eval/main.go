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
		kvs := o.Config.Flatten().Pairs()
		for _, kv := range kvs {
			fmt.Fprintf(w, "%s=%v ", kv.Key, kv.Val)
		}
		fmt.Fprintf(w, "\n")
	}
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

// OutputObservations chooses whether to print or output observations
// depending on outFile flag value
func OutputObservations(outFile string, obs []eval.Observation) error {
	if outFile == "" {
		printObservations(os.Stdout, obs)
		return nil
	}
	return writeObservations(outFile, obs)
}

func suiteFlags() []cli.Flag {
	return []cli.Flag{
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
	}
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
	Flags: append(suiteFlags(), &cli.BoolFlag{
		Name:  "unstable",
		Usage: "use unstable writes in baseline systems",
	}),
	Before: beforeBench,
	Action: func(c *cli.Context) error {
		eval.PrepareBenchmarks()
		suite := initializeSuite(c)
		suite.Filesystems =
			eval.BasicFilesystems(c.String("disk"), c.Bool("unstable"))
		suite.Benches = eval.BenchSuite
		obs := suite.Run()
		err := OutputObservations(c.String("out"), obs)
		return err
	},
}

var scaleCommand = &cli.Command{
	Name:  "scale",
	Usage: "benchmark smallfile with varying clients",
	Flags: append(suiteFlags(), &cli.IntFlag{
		Name:  "threads",
		Value: 10,
		Usage: "maximum number of threads to run till",
	}, &cli.StringFlag{
		Name:  "benchtime",
		Value: "10s",
		Usage: "duration to run each benchmark",
	}),
	Before: beforeBench,
	Action: func(c *cli.Context) error {
		suite := initializeSuite(c)
		suite.Filesystems =
			eval.BasicFilesystems(c.String("disk"), c.Bool("unstable"))
		suite.Benches = eval.ScaleSuite(c.String("benchtime"), c.Int("threads"))
		obs := suite.Run()
		err := OutputObservations(c.String("out"), obs)
		return err
	},
}

var largefileCommand = &cli.Command{
	Name:   "largefile",
	Usage:  "benchmark largefile on many filesystem configurations",
	Flags:  suiteFlags(),
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
		err := OutputObservations(c.String("out"), obs)
		return err
	},
}

func main() {
	app := &cli.App{
		Usage: "run benchmarks",
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