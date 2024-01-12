package compile_test

import (
	"testing"

	dirfs "github.com/mit-pdos/daisy-nfsd/dafnygen/DirFs"
	"github.com/mit-pdos/daisy-nfsd/nfsd"
	"github.com/mit-pdos/go-nfsd/nfstypes"
	"github.com/stretchr/testify/assert"
	"github.com/tchajed/goose/machine/disk"
)

func RootFh() nfstypes.Nfs_fh3 {
	rootfh := nfsd.Fh{Ino: dirfs.Companion_DirFilesys_.RootIno()}
	return rootfh.MakeFh3()
}

func newNfs() *nfsd.Nfs {
	d := disk.NewMemDisk(10_000)
	return nfsd.MakeNfs(d, false)
}

// regression test for bug reported by rtm
func TestNfsRemoveDir(t *testing.T) {
	nfs := newNfs()

	{
		r := nfs.NFSPROC3_MKDIR(nfstypes.MKDIR3args{
			Where: nfstypes.Diropargs3{
				Dir:  RootFh(),
				Name: "foo",
			},
			Attributes: nfstypes.Sattr3{},
		})
		assert.Equal(t, nfstypes.NFS3_OK, r.Status)
	}

	{
		r := nfs.NFSPROC3_REMOVE(nfstypes.REMOVE3args{
			Object: nfstypes.Diropargs3{
				Dir:  RootFh(),
				Name: "foo",
			},
		})
		assert.Equal(t, nfstypes.NFS3ERR_ISDIR, r.Status)
	}
}

func TestNfsWriteSizeMismatch(t *testing.T) {
	nfs := newNfs()
	r := nfs.NFSPROC3_CREATE(nfstypes.CREATE3args{
		Where: nfstypes.Diropargs3{
			Dir:  RootFh(),
			Name: "foo",
		},
		How: nfstypes.Createhow3{
			Mode:           nfstypes.UNCHECKED,
			Obj_attributes: nfstypes.Sattr3{},
			Verf:           [8]byte{},
		},
	})

	// count is larger than data provided
	r2 := nfs.NFSPROC3_WRITE(nfstypes.WRITE3args{
		File:   r.Resok.Obj.Handle,
		Offset: 0,
		Count:  100,
		Stable: nfstypes.FILE_SYNC,
		Data:   []byte{1, 2, 3},
	})

	assert.Equal(t, nfstypes.NFS3_OK, r2.Status)
	assert.Equal(t, nfstypes.Count3(3), r2.Resok.Count)
}
