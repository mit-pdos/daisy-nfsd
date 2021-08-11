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

func (fs Fs) scriptName() string {
	return path.Base(fs.scriptPath)
}

func (fs Fs) Run(command []string) []string {
	args := shellArgs(fs.opts.Delete("name").Pairs())
	args = append(args, command...)
	cmd := exec.Command(fs.scriptPath, args...)
	cmd.Stderr = os.Stderr
	out, err := cmd.Output()
	if err != nil {
		panic(fmt.Sprintf("%s %s failed\n: %v",
			fs.scriptName(), strings.Join(args, " "), err))
	}
	return strings.Split(string(out), "\n")
}

func GetFilesys(conf KeyValue) Fs {
	name := conf["name"].(string)
	fs := Fs{opts: conf}
	switch name {
	case "linux":
		fs.scriptPath = path.Join(goNfsdPath(), "bench", "run-linux.sh")
	case "go-nfsd":
		fs.scriptPath = path.Join(goNfsdPath(), "bench", "run-go-nfsd.sh")
	case "fscq":
		fs.scriptPath = path.Join(goNfsdPath(), "bench", "run-fscq.sh")
	case "daisy-nfsd":
		fs.scriptPath = path.Join(daisyNfsdPath(), "bench", "run-daisy-nfsd.sh")
	}
	return fs
}
