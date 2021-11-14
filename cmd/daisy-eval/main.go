package main

import (
	"compress/gzip"
	"fmt"
	"io"
	"os"
	"path"
	"strings"
	"time"

	"github.com/mit-pdos/daisy-nfsd/eval"
	"github.com/pkg/errors"
	"github.com/schollz/progressbar/v3"
	"github.com/urfave/cli/v2"
)

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
	&cli.DurationFlag{
		Name:  "wait",
		Value: 0,
		Usage: "time to wait between workloads",
	},
	&cli.StringFlag{
		Name:  "disk",
		Value: ":memory:",
		Usage: "path to disk file to use for all benchmarks " +
			"(:memory: uses tmpfs or MemFs as appropriate)",
	},
	&cli.StringFlag{
		Name:  "dir",
		Value: "",
		Usage: "Directory to output to. " +
			"Filename will be based on benchmark suite name.",
	},
	&cli.StringFlag{
		Name:  "out",
		Value: "",
		Usage: "file to output to, overwriting -dir",
	},
	&cli.StringFlag{
		Name:  "filesystems",
		Value: "basic",
		Usage: "suite of filesystems to run " +
			"(basic, durability, " +
			"or comma-separated list like daisy-nfsd,linux,go-nfsd)",
	},
	&cli.StringFlag{
		Name:  "jrnlpatch",
		Value: "",
		Usage: "patch to apply to go-journal before running benchmark",
	},
}

// WriteObservations saves observations in JSON (possibly compressed) to a file
func writeObservations(outFile string, obs <-chan eval.Observation) error {
	var out io.WriteCloser
	out, err := os.Create(outFile)
	if err != nil {
		return fmt.Errorf("could not create output file %s: %v",
			outFile, err)
	}
	if strings.HasSuffix(outFile, ".gz") {
		out = gzip.NewWriter(out)
	}
	for o := range obs {
		eval.WriteObservation(out, o)
	}
	err = out.Close()
	return err
}

// OutputObservations outputs based on flags
func OutputObservations(c *cli.Context, obs <-chan eval.Observation) error {
	// -out takes precedence
	outFile := c.String("out")
	if outFile == "" {
		outDir := c.String("dir")
		if outDir != "" {
			outFile = path.Join(outDir,
				fmt.Sprintf("%s.json", c.Command.Name))
		}
	}
	return writeObservations(outFile, obs)
}

func initializeSuite(c *cli.Context) *eval.BenchmarkSuite {
	return &eval.BenchmarkSuite{
		Iters:     c.Int("iters"),
		Randomize: c.Bool("randomize"),
	}
}

func beforeBench(c *cli.Context) error {
	if c.String("dir") != "" {
		s, err := os.Stat(c.String("dir"))
		if err != nil {
			return errors.Wrap(err, "could not open -dir")
		}
		if !s.Mode().IsDir() {
			return errors.New("-dir is not a directory")
		}
	}
	eval.PrepareBenchmarks()
	return nil
}

func cliFilesystems(c *cli.Context) []eval.KeyValue {
	fss := c.String("filesystems")
	if fss == "basic" {
		fss = "daisy-nfsd,linux,go-nfsd"
	}
	if fss == "durability" {
		return eval.ManyDurabilityFilesystems(c.String("disk"))
	}
	var configs []eval.KeyValue
	fsNames := strings.Split(fss, ",")
	for _, name := range fsNames {
		configs = append(configs,
			eval.BasicFilesystem(
				name, c.String("disk"), c.Bool("unstable"), c.String("jrnlpatch")))
	}
	return configs
}

func runSuite(c *cli.Context, suite *eval.BenchmarkSuite) error {
	ws := suite.Workloads()
	bar := progressbar.NewOptions(len(ws),
		progressbar.OptionSetPredictTime(true),
		progressbar.OptionShowCount(),
		progressbar.OptionEnableColorCodes(true),
		progressbar.OptionOnCompletion(func() {
			fmt.Fprint(os.Stderr, "\n")
		}),
		progressbar.OptionSetWriter(os.Stderr),
		progressbar.OptionThrottle(65*time.Millisecond),
		progressbar.OptionFullWidth(),
	)
	waitTime := c.Duration("wait")
	obs := make(chan eval.Observation)
	go func() {
		for !bar.IsFinished() {
			bar.RenderBlank()
			time.Sleep(500 * time.Millisecond)
		}
	}()
	go func() {
		bar.RenderBlank()
		for _, w := range ws {
			bar.Describe(fmt.Sprintf("running %s on [green]%s[reset]",
				w.Bench.Name(), w.Fs.Name()))
			newObs := w.Run()
			time.Sleep(waitTime)
			bar.Add(1)
			for _, o := range newObs {
				obs <- o
			}
		}
		close(obs)
		bar.Finish()
	}()
	err := OutputObservations(c, obs)
	return err
}

var benchCommand = &cli.Command{
	Name:  "bench",
	Usage: "run a few single-threaded benchmarks",
	Flags: []cli.Flag{&cli.BoolFlag{
		Name:  "unstable",
		Value: false,
		Usage: "use unstable writes in baseline systems",
	}, &cli.IntFlag{
		Name:  "threads",
		Value: 1,
		Usage: "additionally run smallfile with this number of threads",
	}, &cli.StringFlag{
		Name:  "benchtime",
		Usage: "smallfile duration",
		Value: "20s",
	}},
	Before: beforeBench,
	Action: func(c *cli.Context) error {
		eval.PrepareBenchmarks()
		suite := initializeSuite(c)
		suite.Filesystems = cliFilesystems(c)
		suite.Benches = eval.BenchSuite(c.String("benchtime"), c.Int("threads"))
		return runSuite(c, suite)
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
		suite.Filesystems = cliFilesystems(c)
		suite.Benches = eval.ScaleSuite(c.String("benchtime"), c.Int("threads"))
		return runSuite(c, suite)
	},
}

var largefileCommand = &cli.Command{
	Name:   "largefile",
	Usage:  "benchmark largefile on many filesystem configurations",
	Before: beforeBench,
	Action: func(c *cli.Context) error {
		suite := initializeSuite(c)
		suite.Filesystems = cliFilesystems(c)
		suite.Benches = eval.LargefileSuite
		return runSuite(c, suite)
	},
}

var txnbenchCommand = &cli.Command{
	Name:  "txnbench",
	Usage: "run a txn layer benchmark",
	Flags: []cli.Flag{&cli.IntFlag{
		Name:  "threads",
		Value: 40,
		Usage: "maximum number of threads to run till",
	}, &cli.StringFlag{
		Name:  "benchtime",
		Usage: "smallfile duration",
		Value: "20s",
	}},
	Before: beforeBench,
	Action: func(c *cli.Context) error {
		eval.PrepareBenchmarks()
		suite := initializeSuite(c)
		suite.Filesystems = eval.NullFilesystems()
		suite.Benches = eval.TxnBenchSuite(
			c.String("benchtime"), c.Int("threads"), c.String("disk"), c.String("jrnlpatch"))
		return runSuite(c, suite)
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
			txnbenchCommand,
		},
	}
	err := app.Run(os.Args)
	if err != nil {
		fmt.Fprintln(os.Stderr, err.Error())
		os.Exit(1)
	}
}
