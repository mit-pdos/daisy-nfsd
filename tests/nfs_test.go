package compile_test

import (
	"testing"

	dirfs "github.com/mit-pdos/daisy-nfsd/dafnygen/DirFs_Compile"
	"github.com/mit-pdos/daisy-nfsd/nfsd"
	"github.com/mit-pdos/go-nfsd/nfstypes"
	"github.com/stretchr/testify/assert"
	"github.com/tchajed/goose/machine/disk"
)

func RootFh() nfstypes.Nfs_fh3 {
	rootfh := nfsd.Fh{Ino: dirfs.Companion_DirFilesys_.RootIno()}
	return rootfh.MakeFh3()
}

// regression test for bug reported by rtm
func TestNfsRemoveDir(t *testing.T) {
	d := disk.NewMemDisk(10_000)
	nfs := nfsd.MakeNfs(d)

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
