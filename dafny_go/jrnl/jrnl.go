package jrnl

import (
	"github.com/mit-pdos/daisy-nfsd/dafny_go/bytes"
	"github.com/mit-pdos/go-journal/addr"
	"github.com/mit-pdos/go-journal/txn"
	"github.com/tchajed/goose/machine/disk"
)

type Disk = disk.Disk

type Companion_DefaultStruct struct{}

var Companion_Default___ = Companion_DefaultStruct{}

func (_ Companion_DefaultStruct) DiskSize(d *Disk) uint64 {
	return (*d).Size()
}

type Blkno = uint64
type Txn struct {
	txn *txn.Txn
}

func dafnyAddrToAddr(a Addr) addr.Addr {
	return addr.Addr{Blkno: a.Blkno, Off: a.Off}
}

type Jrnl struct {
	log *txn.Log
}

func NewJrnl(d *Disk) *Jrnl {
	return &Jrnl{log: txn.Init(*d)}
}

func (jrnl *Jrnl) Begin() *Txn {
	return &Txn{txn: txn.Begin(jrnl.log)}
}

func (txn *Txn) Read(a Addr, sz uint64) *bytes.Bytes {
	a_ := dafnyAddrToAddr(a)
	buf := txn.txn.ReadBuf(a_, sz)
	return &bytes.Bytes{Data: buf}
}

func (txn *Txn) ReadBit(a Addr) bool {
	a_ := dafnyAddrToAddr(a)
	return txn.txn.ReadBufBit(a_)
}

func (txn *Txn) Write(a Addr, bs *bytes.Bytes) {
	a_ := dafnyAddrToAddr(a)
	txn.txn.OverWrite(a_, bs.Len()*8, bs.Data)
}

func (txn *Txn) WriteBit(a Addr, b bool) {
	a_ := dafnyAddrToAddr(a)
	txn.txn.OverWriteBit(a_, b)
}

func (txn *Txn) Commit() bool {
	ok := txn.txn.Commit()
	return ok
}

func (txn *Txn) Abort() {
	txn.txn.ReleaseAll()
}

func (txn *Txn) NDirty() uint64 {
	return txn.txn.NDirty()
}
