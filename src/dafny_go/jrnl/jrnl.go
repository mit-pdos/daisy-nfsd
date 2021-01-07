package jrnl

import (
	"github.com/mit-pdos/dafny-jrnl/src/dafny_go/bytes"
	"github.com/mit-pdos/goose-nfsd/addr"
	"github.com/mit-pdos/goose-nfsd/buftxn"
	"github.com/mit-pdos/goose-nfsd/txn"
	"github.com/tchajed/goose/machine/disk"
)

type Disk = disk.Disk
type Blkno = uint64
type Txn struct {
	btxn *buftxn.BufTxn
}

type Addr_Addr struct {
	Blkno Blkno
	Off   uint64
}

type Addr struct {
	Addr_Addr
}

func (_this Addr) Dtor_blkno() uint64 {
	return _this.Addr_Addr.Blkno
}

func (_this Addr) Dtor_off() uint64 {
	return _this.Addr_Addr.Off
}

func dafnyAddrToAddr(a Addr) addr.Addr {
	return addr.Addr{Blkno: a.Blkno, Off: a.Off}
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

func (txn *Txn) Read(a Addr, sz uint64) *bytes.Bytes {
	buf := txn.btxn.ReadBuf(dafnyAddrToAddr(a), sz)
	return &bytes.Bytes{Data: buf.Data}
}

func (txn *Txn) Write(a Addr, bs *bytes.Bytes) {
	txn.btxn.OverWrite(dafnyAddrToAddr(a), bs.Len()*8, bs.Data)
}

// TODO: wrap read/write bit

func (txn *Txn) Commit() {
	txn.btxn.CommitWait(true)
}
