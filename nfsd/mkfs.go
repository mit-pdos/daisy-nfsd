package nfsd

import (
	dirfs "github.com/mit-pdos/dafny-nfsd/dafnygen/DirFs_Compile"
	std "github.com/mit-pdos/dafny-nfsd/dafnygen/Std_Compile"

	"github.com/tchajed/goose/machine/disk"
)

type Nfs struct {
	filesys *dirfs.DirFilesys
}

func MakeNfs(d disk.Disk) *Nfs {
	dfsopt := dirfs.Companion_DirFilesys_.New(&d)
	if dfsopt.Is_None() {
		panic("no dirfs")
	}

	dfs := dfsopt.Get().(std.Option_Some).X.(*dirfs.DirFilesys)

	nfs := &Nfs{
		filesys: dfs,
	}

	return nfs
}
