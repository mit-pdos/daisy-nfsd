package jrnl

import (
	"github.com/mit-pdos/goose-nfsd/buftxn"
	"github.com/mit-pdos/goose-nfsd/txn"
	"github.com/tchajed/goose/machine/disk"
)

type Disk = disk.Disk
type Txn struct {
	btxn *buftxn.BufTxn
}

type Jrnl struct {
	txn *txn.Txn
}

func NewJrnl(d *Disk) *Jrnl {
	return &Jrnl{txn: txn.MkTxn(*d)}
}

func (jrnl *Jrnl) Begin() *Txn {
	return &Txn{btxn: buftxn.Begin(jrnl.txn)}
}

// TODO: wrap read/write
//
// TODO: how do we get an Addr?
// If we export one to Dafny, it'll be slightly less convenient since it won't
// have fields. If we use the Dafny datatype then we need this library to depend
// on auto-generated code.

func (txn *Txn) Commit() {
	txn.btxn.CommitWait(true)
}
