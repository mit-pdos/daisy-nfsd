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

func NewJrnl(d Disk) *Jrnl {
	return &Jrnl{txn: txn.MkTxn(d)}
}

func (jrnl *Jrnl) Begin() Txn {
	return Txn{btxn: buftxn.Begin(jrnl.txn)}
}

// TODO: wrap read/write

func (txn Txn) Commit() {
	txn.btxn.CommitWait(true)
}
