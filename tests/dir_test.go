package compile_test

import (
	"testing"

	"github.com/mit-pdos/dafny-jrnl/dafny_go/jrnl"
	dirents "github.com/mit-pdos/dafny-jrnl/dafnygen/DirEntries_Compile"
	dirfs "github.com/mit-pdos/dafny-jrnl/dafnygen/DirFs_Compile"
	std "github.com/mit-pdos/dafny-jrnl/dafnygen/Std_Compile"
	_dafny "github.com/mit-pdos/dafny-jrnl/dafnygen/dafny"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"github.com/tchajed/goose/machine/disk"
)

func NewFs() *dirfs.DirFilesys {
	var d disk.Disk = disk.NewMemDisk(100_000)
	dfsopt := dirfs.Companion_DirFilesys_.New(&d)
	if dfsopt.Is_None() {
		panic("no dirfs")
	}
	dfs := dfsopt.Get().(std.Option_Some).X.(*dirfs.DirFilesys)
	return dfs
}

func seqOfString(s string) _dafny.Seq {
	xs_i := make([]interface{}, len(s))
	for i, x := range []byte(s) {
		xs_i[i] = x
	}
	return _dafny.SeqOf(xs_i...)
}

func Begin(fs *dirfs.DirFilesys) *jrnl.Txn {
	return fs.Fs().Jrnl().Begin()
}

var rootIno = dirfs.Companion_DirFilesys_.RootIno()

func TestDirFsLookup(t *testing.T) {
	fs := NewFs()
	txn := Begin(fs)
	defer txn.Abort()
	r := fs.CREATE(txn, rootIno, seqOfString("foo"))
	require.True(t, r.Is_Ok(), "CreateFile should succeed")
	ino := r.Val().(uint64)

	r2 := fs.LOOKUP(txn, rootIno, seqOfString("foo"))
	require.True(t, r.Is_Ok(), "Lookup should succeed")
	ino2 := r2.Val().(uint64)
	assert.Equal(t, ino, ino2, "lookup should return correct result")
}

func TestPathEncode(t *testing.T) {
	s := seqOfString("foo")
	s2 := dirents.Companion_Default___.DecodeEncodeTest(s)
	assert.Equal(t, s2.LenInt(), int(3), "decoded string is short")
}
