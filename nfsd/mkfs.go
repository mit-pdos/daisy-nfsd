package nfsd

import (
	"os/user"
	"strconv"

	"github.com/mit-pdos/daisy-nfsd/dafny_go/bytes"
	"github.com/mit-pdos/daisy-nfsd/dafny_go/jrnl"
	dirfs "github.com/mit-pdos/daisy-nfsd/dafnygen/DirFs"
	fskinds "github.com/mit-pdos/daisy-nfsd/dafnygen/FsKinds"

	"github.com/tchajed/goose/machine/disk"
)

type Nfs struct {
	// the Dafny Filesys class
	filesys *dirfs.DirFilesys

	// read-only
	uid         uint32
	gid         uint32
	asyncWrites bool

	// stats
	//
	// number of calls to each operation, indexed by procedure numbers from RFC
	// 1813
	opCounts [NUM_NFS_OPS]uint32
	opNanos  [NUM_NFS_OPS]uint64
}

func zeroDisk(d disk.Disk) {
	zeroblock := make([]byte, 4096)
	sz := d.Size()
	for i := uint64(0); i < sz; i++ {
		d.Write(i, zeroblock)
	}
	d.Barrier()
}

func getUser() (uid uint32, gid uint32) {
	u, err := user.Current()
	if err != nil {
		panic("no user")
	}
	uid_i, err := strconv.Atoi(u.Uid)
	if err != nil {
		panic("could not parse user uid")
	}
	gid_i, err := strconv.Atoi(u.Gid)
	if err != nil {
		panic("could not parse user gid")
	}
	return uint32(uid_i), uint32(gid_i)
}

func correctMagic(d disk.Disk) bool {
	super_blk := fskinds.Companion_Default___.SuperBlkAddr().Blkno
	bs := d.Read(super_blk)
	return fskinds.Companion_SuperBlock_.CorrectMagic(&bytes.Bytes{Data: bs})
}

func MakeNfs(d disk.Disk, force bool) *Nfs {
	if !force {
		if correctMagic(d) {
			panic("disk seems to already have an initialized DaisyNFS file system")
		}
	}
	// TODO: this is a bit dangerous (the above only prevents overwriting a
	// DaisyNFS file system, but not some other important file)
	zeroDisk(d)

	uid, gid := getUser()

	dfsopt := dirfs.Companion_DirFilesys_.New(&d, uid, gid)
	if dfsopt.Is_None() {
		panic("no dirfs")
	}

	dfs := dfsopt.Dtor_x().(*dirfs.DirFilesys)

	nfs := &Nfs{
		filesys: dfs,
		uid:     uid,
		gid:     gid,
	}

	return nfs
}

func RecoverNfs(d disk.Disk) *Nfs {
	jrnl := jrnl.NewJrnl(&d)
	dfs := dirfs.New_DirFilesys_()
	dfs.Recover(jrnl)

	uid, gid := getUser()

	nfs := &Nfs{
		filesys: dfs,
		uid:     uid,
		gid:     gid,
	}

	return nfs
}

func (nfs *Nfs) SetAsync(asyncWrites bool) {
	nfs.asyncWrites = asyncWrites
}
