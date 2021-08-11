package eval

import (
	"fmt"
	"regexp"
	"strconv"
)

type Benchmark interface {
	// Opts has configuration related to the benchmark workload under test
	// (including bench, the benchmark name, and also eg, size in largefile)
	Opts() KeyValue

	// Command to run this benchmark
	//
	// does not include file system
	Command() []string

	// ParseOutput converts the output of the benchmark to a set of observations
	ParseOutput(lines []string) []Observation
}

type regexBench struct {
	opts  KeyValue
	regex *regexp.Regexp
}

func (b regexBench) Opts() KeyValue {
	return b.opts
}

// goArgs converts key-value pairs to options using Go's flag syntax for
// arguments, where KeyValue{"key": "value"} would be passed as -key=value.
func goArgs(kvs []keyValuePair) []string {
	var args []string
	for _, kv := range kvs {
		args = append(args, fmt.Sprintf("-%s=%v", kv.key, kv.val))
	}
	return args
}

func (b regexBench) Command() []string {
	return goArgs(b.opts.Pairs())
}

// parseLineResult matches against a line to identify a benchmark and value
//
// interpreting the value is left to the caller, based on the benchmark
func (b regexBench) parseLineResult(line string) (bench string, val float64,
	ok bool) {
	matches := b.regex.FindStringSubmatch(line)
	if matches == nil {
		ok = false
		return
	}
	bench_i := b.regex.SubexpIndex("bench")
	bench = matches[bench_i]
	val_i := b.regex.SubexpIndex("val")
	var err error
	val, err = strconv.ParseFloat(matches[val_i], 10)
	if err != nil {
		panic(fmt.Sprintf("unexpected number %v", matches[val_i]))
	}
	ok = true
	return
}

// parseLine translates one line of output to maybe one observation
func (b regexBench) lineToObservation(line string) (o Observation, ok bool) {
	bench, val, ok := b.parseLineResult(line)
	if !ok {
		return Observation{}, false
	}
	conf := b.opts.Clone()
	conf["bench"] = bench
	return Observation{
		Config: conf,
		Values: KeyValue{"val": val},
	}, true
}

func (b regexBench) ParseOutput(lines []string) []Observation {
	var obs []Observation
	for _, line := range lines {
		o, ok := b.lineToObservation(line)
		if ok {
			obs = append(obs, o)
		}
	}
	return obs
}

func benchFromRegex(opts KeyValue, r string) Benchmark {
	return regexBench{opts: opts, regex: regexp.MustCompile(r)}
}

func LargefileBench(fileSizeMb int) Benchmark {
	return benchFromRegex(
		KeyValue{"file-size": float64(fileSizeMb)},
		`fs-(?P<bench>largefile):.* throughput (?P<val>[0-9.]*) MB/s`,
	)
}

func SmallfileBench(threads int) Benchmark {
	return benchFromRegex(
		KeyValue{
			"start":   float64(threads),
			"threads": float64(threads),
		},
		`fs-(?P<bench>smallfile): [0-9]+ (?P<val>[0-9.]*) file/sec`,
	)
}

func AppBench() Benchmark {
	return benchFromRegex(
		KeyValue{},
		`(?P<bench>app)-bench (?P<val>[0-9.]*) app/s`,
	)
}
