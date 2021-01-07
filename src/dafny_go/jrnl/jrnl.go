package jrnl

import "github.com/mit-pdos/goose-nfsd/txn"

type Jrnl struct {
	txn *txn.Txn
}
