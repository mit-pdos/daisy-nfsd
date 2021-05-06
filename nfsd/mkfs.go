package nfsd

import (
	"os/user"
	"strconv"

	"github.com/mit-pdos/dafny-nfsd/dafny_go/jrnl"
	dirfs "github.com/mit-pdos/dafny-nfsd/dafnygen/DirFs_Compile"

	"github.com/tchajed/goose/machine/disk"
)

type Nfs struct {
	filesys *dirfs.DirFilesys
	uid     int
	gid     int
}

func zeroDisk(d disk.Disk) {
	zeroblock := make([]byte, 4096)
	sz := d.Size()
	for i := uint64(0); i < sz; i++ {
		d.Write(i, zeroblock)
	}
	d.Barrier()
}

func getUser() (uid int, gid int) {
	u, err := user.Current()
	if err != nil {
		panic("no user")
	}
	uid, err = strconv.Atoi(u.Uid)
	if err != nil {
		panic("could not user uid")
	}
	uid, err = strconv.Atoi(u.Gid)
	if err != nil {
		panic("could not user gid")
	}
	return
}

func MakeNfs(d disk.Disk) *Nfs {
	zeroDisk(d)
	dfsopt := dirfs.Companion_DirFilesys_.New(&d)
	if dfsopt.Is_None() {
		panic("no dirfs")
	}

	dfs := dfsopt.Dtor_x().(*dirfs.DirFilesys)

	uid, gid := getUser()

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
