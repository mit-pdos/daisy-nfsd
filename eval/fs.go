package eval

import (
	"fmt"
	"os"
	"os/exec"
	"path"
	"strings"
)

func getEnvDir(envvar string) string {
	val := os.Getenv(envvar)
	if val == "" {
		panic(fmt.Sprintf("environment variable %v not set", envvar))
	}
	s, err := os.Stat(val)
	if err != nil {
		panic(fmt.Sprintf("could not lookup %v: %v", envvar, err))
	}
	if !s.Mode().IsDir() {
		panic(fmt.Errorf("%v is not a directory", envvar))
	}
	return val
}

// shorthands to avoid misspellings

func goNfsdPath() string {
	return getEnvDir("GO_NFSD_PATH")
}

func daisyNfsdPath() string {
	return getEnvDir("DAISY_NFSD_PATH")
}

func xv6Path() string {
	return getEnvDir("XV6_PATH")
}

// shellArgs returns kvs treating the keys as argument names,
// with shell script arguments: each option must have an argument,
// which is supplied as the next argument.
//
// Each key is prefixed with an additional hyphen, so for example
// KeyValue{"disk": "/dev/shm/disk.img"} will become -disk /dev/shm/disk.img.
func shellArgs(kvs []KeyValuePair) []string {
	var args []string
	for _, pair := range kvs {
		args = append(args,
			"-"+pair.Key, // the key is an option name
			fmt.Sprintf("%v", pair.Val))
	}
	return args
}

type Fs struct {
	scriptPath string
	opts       KeyValue
}

func (fs Fs) Name() string {
	return fs.opts["name"].(string)
}

func (fs Fs) scriptName() string {
	return path.Base(fs.scriptPath)
}

func (fs Fs) Run(command []string) []string {
	args := shellArgs(fs.opts.Delete("name").Pairs())
	for _, cmdArg := range command {
		args = append(args, os.ExpandEnv(cmdArg))
	}
	cmd := exec.Command(os.ExpandEnv(fs.scriptPath), args...)
	out, err := cmd.Output()
	if err != nil {
		fmt.Fprintf(os.Stderr, "%s %s failed\n", fs.scriptName(),
			strings.Join(args, " "))
		if err, ok := err.(*exec.ExitError); ok {
			fmt.Fprintf(os.Stderr, "%s", string(err.Stderr))
		}
		os.Exit(cmd.ProcessState.ExitCode())
	}
	return strings.Split(string(out), "\n")
}

func GetFilesys(conf KeyValue) Fs {
	name := conf["name"].(string)
	fs := Fs{opts: conf}
	switch name {
	case "linux":
		fs.scriptPath = path.Join("${GO_NFSD_PATH}", "bench", "run-linux.sh")
	case "go-nfsd":
		fs.scriptPath = path.Join("${GO_NFSD_PATH}", "bench", "run-go-nfsd.sh")
	case "fscq":
		// check this because it's a dependency
		_ = getEnvDir("FSCQ_PATH")
		fs.scriptPath = path.Join(goNfsdPath(), "bench", "run-fscq.sh")
	case "daisy-nfsd":
		fs.scriptPath = path.Join("${DAISY_NFSD_PATH}",
			"bench", "run-daisy-nfsd.sh")
	}
	return fs
}
