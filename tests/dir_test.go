package compile_test

import (
	"fmt"
	"strings"
	"testing"

	"github.com/mit-pdos/daisy-nfsd/dafny_go/bytes"
	dirents "github.com/mit-pdos/daisy-nfsd/dafnygen/DirEntries_Compile"
	dirfs "github.com/mit-pdos/daisy-nfsd/dafnygen/DirFs_Compile"
	lock_order "github.com/mit-pdos/daisy-nfsd/dafnygen/LockOrder_Compile"
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

func createRootFile(fs *dirfs.DirFilesys, name string) uint64 {
	txn := fs.Begin()
	r := fs.CREATE(txn, rootIno, stringToBytes(name), nfs_spec.Companion_CreateHow3_.Create_Unchecked_(
		nfs_spec.Companion_Sattr3_.SetNone(),
	))
	if !r.Is_Ok() {
		panic(fmt.Errorf("create failed with %v", r.Dtor_err()))
	}
	txn.Commit(true)
	return r.Dtor_v().(nfs_spec.CreateResult).Dtor_ino()
}

func TestDirFsLookup(t *testing.T) {
	fs := NewFs()
	txn := fs.Begin()
	r := fs.CREATE(txn, rootIno, stringToBytes("foo"),
		nfs_spec.Companion_CreateHow3_.Create_Unchecked_(
			nfs_spec.Companion_Sattr3_.SetNone(),
		))
	r = dirfs.Companion_Default___.HandleResult(r, txn, true)
	require.True(t, r.Is_Ok(), "CreateFile should succeed")
	ino := r.Dtor_v().(nfs_spec.CreateResult).Dtor_ino()

	txn = fs.Begin()
	r, _ = fs.LOOKUP(txn, rootIno, stringToBytes("foo"))
	r = dirfs.Companion_Default___.HandleResult(r, txn, true)
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
	r, _ := fs.LOOKUP(txn, 1<<60, stringToBytes("foo"))
	txn.Abort()
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
	txn.Abort()
}

func TestLockInsert(t *testing.T) {
	locks := lock_order.Companion_Default___.EmptyLockHint()
	locks = lock_order.Companion_Default___.Insert__lock__hint(locks, 3)
	assert.True(t, lock_order.Companion_Default___.Has__lock(locks, 3),
		"inserting doesn't work")
	assert.True(t, lock_order.Companion_Default___.Safe__lock(locks, 3),
		"inserting is not safe")
}

func TestRenameLockOrder(t *testing.T) {
	fs := NewFs()
	srcIno := createRootFile(fs, "foo")
	dstIno := createRootFile(fs, "bar")
	if srcIno >= dstIno {
		panic("failed to create inodes in the right order")
	}
	locks := lock_order.Companion_Default___.EmptyLockHint()
	txn := fs.Begin()
	r := fs.RENAME(txn, locks,
		rootIno, stringToBytes("bar"),
		rootIno, stringToBytes("foo"))
	require.True(t, r.Is_Err() && r.Dtor_err().Is_LockOrderViolated(),
		"should return correct error")
	locks = r.Dtor_err().Dtor_locks()
	txn.Abort()

	txn = fs.Begin()
	r = fs.RENAME(txn, locks,
		rootIno, stringToBytes("bar"),
		rootIno, stringToBytes("foo"))
	if r.Is_Err() {
		require.Fail(t, "rename with correct lock hints errored: %v", r.Dtor_err().Nfs3__code())
	}
	txn.Commit(true)
}
