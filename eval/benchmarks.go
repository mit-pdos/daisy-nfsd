package eval

import (
	"fmt"
	"os"
	"os/exec"
	"path"
	"regexp"
	"strconv"
)

type Benchmark struct {
	command []string
	// Config has configuration related to the benchmark workload under test
	// "bench" is a map with benchmark options
	Config KeyValue
	regex  *regexp.Regexp
}

func (b Benchmark) Name() string {
	return b.Config["name"].(string)
}

// goArgs converts key-value pairs to options using Go's flag syntax for
// arguments, where KeyValue{"key": "value"} would be passed as -key=value.
func goArgs(kvs []KeyValuePair) []string {
	var args []string
	for _, kv := range kvs {
		args = append(args, fmt.Sprintf("-%s=%v", kv.Key, kv.Val))
	}
	return args
}

func (b Benchmark) Command() []string {
	var args []string
	args = append(args, b.command...)
	opts := b.Config["bench"].(KeyValue)
	args = append(args, goArgs(opts.Pairs())...)
	return args
}

// parseLineResult matches against a line to identify a benchmark and value
//
// interpreting the value is left to the caller, based on the benchmark
func (b Benchmark) parseLineResult(line string) (bench string, val float64,
	ok bool) {
	matches := b.regex.FindStringSubmatch(line)
	if matches == nil {
		ok = false
		return
	}
	benchIdx := b.regex.SubexpIndex("bench")
	bench = matches[benchIdx]
	valIdx := b.regex.SubexpIndex("val")
	var err error
	val, err = strconv.ParseFloat(matches[valIdx], 10)
	if err != nil {
		panic(fmt.Sprintf("unexpected number %v", matches[valIdx]))
	}
	ok = true
	return
}

// parseLine translates one line of output to maybe one observation
func (b Benchmark) lineToObservation(line string) (o Observation, ok bool) {
	bench, val, ok := b.parseLineResult(line)
	if !ok {
		return Observation{}, false
	}
	conf := b.Config.Clone()
	conf["bench"].(KeyValue)["name"] = bench
	return Observation{
		Config: conf,
		Values: KeyValue{"val": val},
	}, true
}

func (b Benchmark) ParseOutput(lines []string) []Observation {
	var obs []Observation
	for _, line := range lines {
		o, ok := b.lineToObservation(line)
		if ok {
			obs = append(obs, o)
		}
	}
	return obs
}

func benchFromRegex(command []string, name string,
	opts KeyValue, r string) Benchmark {
	return Benchmark{
		command: command,
		Config:  KeyValue{"bench": opts, "name": name},
		regex:   regexp.MustCompile(r),
	}
}

func LargefileBench(fileSizeMb int) Benchmark {
	return benchFromRegex(
		[]string{"${GO_NFSD_PATH}/fs-largefile"},
		"largefile",
		KeyValue{"file-size": float64(fileSizeMb)},
		`fs-(?P<bench>largefile):.* throughput (?P<val>[0-9.]*) MB/s`,
	)
}

func SmallfileBench(benchtime string, threads int) Benchmark {
	return benchFromRegex(
		[]string{"${GO_NFSD_PATH}/fs-smallfile"},
		"smallfile",
		KeyValue{
			"benchtime": benchtime,
			"start":     float64(threads),
			"threads":   float64(threads),
		},
		`fs-(?P<bench>smallfile): [0-9]+ (?P<val>[0-9.]*) file/sec`,
	)
}

func AppBench() Benchmark {
	return benchFromRegex(
		[]string{path.Join("${GO_NFSD_PATH}", "bench", "app-bench.sh"),
			"${XV6_PATH}",
			"/mnt/nfs"},
		"app",
		KeyValue{},
		`(?P<bench>app)-bench (?P<val>[0-9.]*) app/s`,
	)
}

func PrepareBenchmarks() {
	dir, err := os.Getwd()
	if err != nil {
		panic(err)
	}
	os.Chdir(goNfsdPath())
	err = exec.Command("go", "build",
		"./cmd/fs-largefile").Run()
	if err != nil {
		panic(err)
	}
	err = exec.Command("go", "build",
		"./cmd/fs-smallfile").Run()
	if err != nil {
		panic(err)
	}
	os.Chdir(dir)
}
