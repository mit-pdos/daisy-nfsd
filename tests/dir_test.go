package compile_test

import (
	"strings"
	"testing"

	"github.com/mit-pdos/daisy-nfsd/dafny_go/bytes"
	dirents "github.com/mit-pdos/daisy-nfsd/dafnygen/DirEntries_Compile"
	dirfs "github.com/mit-pdos/daisy-nfsd/dafnygen/DirFs_Compile"
	nfs_spec "github.com/mit-pdos/daisy-nfsd/dafnygen/Nfs_Compile"
	std "github.com/mit-pdos/daisy-nfsd/dafnygen/Std_Compile"
	_dafny "github.com/mit-pdos/daisy-nfsd/dafnygen/dafny"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"github.com/tchajed/goose/machine/disk"
)

func NewFs() *dirfs.DirFilesys {
	var d disk.Disk = disk.NewMemDisk(100_000)
	dfsopt := dirfs.Companion_DirFilesys_.New(&d, 0, 0)
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

func stringToBytes(name string) *bytes.Bytes {
	return &bytes.Bytes{Data: []byte(name)}
}

var rootIno = dirfs.Companion_DirFilesys_.RootIno()

func TestDirFsLookup(t *testing.T) {
	fs := NewFs()
	txn := fs.Begin()
	r := fs.CREATE(txn, rootIno, stringToBytes("foo"),
		nfs_spec.Companion_CreateHow3_.Create_Unchecked_(
			nfs_spec.Companion_Sattr3_.SetNone(),
		))
	r = dirfs.Companion_Default___.HandleResult(r, txn)
	require.True(t, r.Is_Ok(), "CreateFile should succeed")
	ino := r.Dtor_v().(nfs_spec.InoResult).Dtor_ino()

	txn = fs.Begin()
	r = fs.LOOKUP(txn, rootIno, stringToBytes("foo"))
	r = dirfs.Companion_Default___.HandleResult(r, txn)
	require.True(t, r.Is_Ok(), "Lookup should succeed")
	ino2 := r.Dtor_v().(nfs_spec.InoResult).Dtor_ino()
	assert.Equal(t, ino, ino2, "lookup should return correct result")
}

func TestPathEncode(t *testing.T) {
	s := seqOfString("foo")
	s2 := dirents.Companion_Default___.DecodeEncodeTest(s)
	assert.Equal(t, s2.LenInt(), int(3), "decoded string is short")
}

// based on a test rtm came up with
func TestInvalidInodeNumber(t *testing.T) {
	fs := NewFs()
	txn := fs.Begin()
	r := fs.LOOKUP(txn, 1<<60, stringToBytes("foo"))
	assert.True(t, r.ErrBadHandle_q(), "should fail with ErrBadHandle")
}

func TestCreateBadNames(t *testing.T) {
	fs := NewFs()
	txn := fs.Begin()
	// the path length limit is 56
	r := fs.CREATE(txn, rootIno, stringToBytes(strings.Repeat("x", 100)),
		nfs_spec.Companion_CreateHow3_.Create_Unchecked_(
			nfs_spec.Companion_Sattr3_.SetNone(),
		))
	assert.True(t, r.Is_Err() && r.Dtor_err().Is_NameTooLong(), "should fail due to long name")

	r = fs.CREATE(txn, rootIno, stringToBytes(""),
		nfs_spec.Companion_CreateHow3_.Create_Unchecked_(
			nfs_spec.Companion_Sattr3_.SetNone(),
		))
	assert.True(t, r.Is_Err() && r.Dtor_err().Is_Inval(), "should fail due to empty name")
}
