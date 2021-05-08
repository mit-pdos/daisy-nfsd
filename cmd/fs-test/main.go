package main

import (
	"flag"
	"fmt"
	"os"
	"reflect"

	"golang.org/x/sys/unix"
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

	err = os.Chdir(mnt)
	assertNoError(err)

	err = os.Mkdir("foo", 0755)
	assertNoError(err)

	fd, err := unix.Open("message.txt", unix.O_CREAT|unix.O_RDWR, 0644)
	assertNoError(err)
	n, err := unix.Pwrite(fd, []byte("hello, "), 0)
	assertNoError(err)
	assertEqual(n, len("hello, "), "short write")
	_, err = unix.Pwrite(fd, []byte("world\n"), int64(n))
	assertNoError(err)
	unix.Fsync(fd)
	unix.Close(fd)

	ents, err = os.ReadDir(".")
	assertNoError(err)
	assertEqual(len(ents), 2)

	_, err = os.ReadDir("message.txt")
	assertIsError(err, "readdir non-dir")

	ents, err = os.ReadDir("foo")
	assertNoError(err, "readdir foo")
	assertEqual(len(ents), 0, "foo is non-empty?")

	contents, err := os.ReadFile("message.txt")
	assertNoError(err, "read message.txt")
	assertEqual(contents, []byte("hello, world\n"), "file has wrong contents")

	err = unix.Rename("message.txt", "msg.txt")
	assertNoError(err, "move file within same directory")
	err = unix.Rename("msg.txt", "foo/msg.txt")
	assertNoError(err, "move file between directories")

	// attempt to delete foo with msg.txt still inside
	err = unix.Rmdir("foo")
	assertIsError(err, "RMDIR on non-empty directory")

	// delete foo/msg.txt and then foo
	err = unix.Unlink("foo/msg.txt")
	assertNoError(err, "REMOVE")
	err = unix.Rmdir("foo")
	assertNoError(err, "RMDIR")
}
