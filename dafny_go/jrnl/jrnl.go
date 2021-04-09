package jrnl

import (
	"github.com/mit-pdos/dafny-nfsd/dafny_go/bytes"
	"github.com/mit-pdos/goose-nfsd/addr"
	"github.com/mit-pdos/goose-nfsd/twophase"
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
	btxn *twophase.TwoPhase
}

func dafnyAddrToAddr(a Addr) addr.Addr {
	return addr.Addr{Blkno: a.Blkno, Off: a.Off}
}

type Jrnl struct {
	tpp *twophase.TwoPhasePre
}

func NewJrnl(d *Disk) *Jrnl {
	tpp := twophase.Init(*d)
	return &Jrnl{tpp}
}

func (jrnl *Jrnl) Begin() *Txn {
	return &Txn{btxn: twophase.Begin(jrnl.tpp)}
}

func (txn *Txn) Read(a Addr, sz uint64) *bytes.Bytes {
	a_ := dafnyAddrToAddr(a)
	buf := txn.btxn.ReadBuf(a_, sz)
	return &bytes.Bytes{Data: buf}
}

func is_bit_set(b byte, off uint64) bool {
	return b&(1<<off) != 0
}

func (txn *Txn) ReadBit(a Addr) bool {
	a_ := dafnyAddrToAddr(a)
	buf := txn.btxn.ReadBuf(a_, 1)
	data := buf[0]
	return is_bit_set(data, a.Off%8)
}

func (txn *Txn) Write(a Addr, bs *bytes.Bytes) {
	a_ := dafnyAddrToAddr(a)
	txn.btxn.OverWrite(a_, bs.Len()*8, bs.Data)
}

func (txn *Txn) WriteBit(a Addr, b bool) {
	a_ := dafnyAddrToAddr(a)
	var data byte
	if b {
		data = 0xFF
	} else {
		data = 0
	}
	txn.btxn.OverWrite(a_, 1, []byte{data})
}

func (txn *Txn) Commit() bool {
	ok := txn.btxn.Commit()
	return ok
}

func (txn *Txn) Abort() {
	txn.btxn.ReleaseAll()
}
