package main

import (
	"flag"
	"fmt"
	"os"
	"path"
	"reflect"
)

func printFormatArgs(args []interface{}) {
	if len(args) > 0 {
		fmtString := args[0].(string)
		fmt.Fprintf(os.Stderr, fmtString+"\n", args[1:]...)
	}
}

func assertEqual(actual interface{}, expected interface{}, msgAndArgs ...interface{}) {
	if !reflect.DeepEqual(actual, expected) {
		fmt.Fprintf(os.Stderr, "%v != %v\n", actual, expected)
		printFormatArgs(msgAndArgs)
		os.Exit(1)
	}
}

func assertNoError(err error, msgAndArgs ...interface{}) {
	if err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		printFormatArgs(msgAndArgs)
		os.Exit(1)
	}
}

func assertIsError(err error, msgAndArgs ...interface{}) {
	if err == nil {
		fmt.Fprintf(os.Stderr, "unexpected success\n")
		printFormatArgs(msgAndArgs)
		os.Exit(1)
	}
}

func main() {
	flag.Parse()
	if flag.NArg() < 1 {
		fmt.Fprintf(os.Stderr, "Usage: fs-test <mount path>\n")
		os.Exit(1)
	}

	mnt := flag.Arg(0)
	ents, err := os.ReadDir(mnt)
	assertNoError(err)
	assertEqual(len(ents), 0)

	err = os.Mkdir(path.Join(mnt, "foo"), 0644)
	assertNoError(err)

	f, err := os.Create(path.Join(mnt, "message.txt"))
	assertNoError(err)
	n, err := f.Write([]byte("hello, "))
	assertNoError(err)
	assertEqual(n, len("hello, "), "short write")
	_, err = f.Write([]byte("world\n"))
	assertNoError(err)
	f.Sync()
	f.Close()

	ents, err = os.ReadDir(mnt)
	assertNoError(err)
	assertEqual(len(ents), 2)

	_, err = os.ReadDir(path.Join(mnt, "message.txt"))
	assertIsError(err, "readdir non-dir")

	ents, err = os.ReadDir(path.Join(mnt, "foo"))
	assertNoError(err, "readdir foo")
	assertEqual(len(ents), 0, "foo is non-empty?")

	contents, err := os.ReadFile(path.Join(mnt, "message.txt"))
	assertNoError(err, "read message.txt")
	assertEqual(contents, []byte("hello, world\n"), "file has wrong contents")

	// will end up being an RMDIR (after REMOVE fails)
	err = os.Remove(path.Join(mnt, "foo"))
	assertNoError(err, "RMDIR")
	// will end up being a REMOVE
	err = os.Remove(path.Join(mnt, "message.txt"))
	assertNoError(err, "REMOVE")
}
