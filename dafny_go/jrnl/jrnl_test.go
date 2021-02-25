package jrnl

import (
	"fmt"
	"testing"

	"github.com/mit-pdos/dafny-jrnl/dafny_go/bytes"
	"github.com/stretchr/testify/assert"
	"github.com/tchajed/goose/machine/disk"
)

// mkAddr builds the Dafny representation of an address
//
// Mainly for testing purposes; Dafny-generated code constructs a datatype using
// a struct literal.
func mkAddr(blkno Blkno, off uint64) Addr {
	if blkno < 513 {
		panic(fmt.Sprintf("invalid blkno %d < 513", blkno))
	}
	if off > 8*4096 {
		panic(fmt.Sprintf("out-of-bounds offset %d", off))
	}
	return Addr{Addr_Addr: Addr_Addr{Blkno: blkno, Off: off}}
}

func TestReadWriteTxn(t *testing.T) {
	assert := assert.New(t)

	var d disk.Disk = disk.NewMemDisk(1000)
	jrnl := NewJrnl(&d)
	data := []byte{1, 2, 3, 4}
	a0 := mkAddr(513, 0)
	a1 := mkAddr(513, 4*8)

	// write initial non-zero data
	{
		txn := jrnl.Begin()
		bs := &bytes.Bytes{Data: data}
		txn.Write(a0, bs)
		txn.Commit()
	}

	// copy it
	{
		txn := jrnl.Begin()
		bs := txn.Read(a0, uint64(len(data))*8)
		txn.Write(a1, bs)
		txn.Commit()
	}

	// read from new location
	{
		txn := jrnl.Begin()
		bs := txn.Read(a1, uint64(len(data))*8)
		assert.Equal(data, bs.Data)
		txn.Commit()
	}
}

func TestReadWriteBits(t *testing.T) {
	assert := assert.New(t)

	var d disk.Disk = disk.NewMemDisk(1000)
	jrnl := NewJrnl(&d)

	correctBit := func(a Addr) bool {
		b := false
		if a.Off%3 == 0 {
			b = true
		}
		if a.Blkno == 513 {
			return b
		}
		return !b
	}

	{
		txn := jrnl.Begin()
		for off := uint64(0); off < 8*4096; off++ {
			a := mkAddr(513, off)
			txn.WriteBit(a, correctBit(a))

			a = mkAddr(514, off)
			txn.WriteBit(a, correctBit(a))
		}
		txn.Commit()
	}

	{
		txn := jrnl.Begin()
		for off := uint64(0); off < 8*4096; off++ {
			a := mkAddr(513, off)
			assert.Equal(correctBit(a), txn.ReadBit(a), "addr %v is incorrect", a)

			a = mkAddr(514, off)
			assert.Equal(correctBit(a), txn.ReadBit(a), "addr %v is incorrect", a)
		}
		txn.Commit()
	}
}

func TestReadModify(t *testing.T) {
	assert := assert.New(t)

	var d disk.Disk = disk.NewMemDisk(1000)
	jrnl := NewJrnl(&d)
	a0 := mkAddr(513, 0)

	{
		txn := jrnl.Begin()
		buf := txn.Read(a0, 4096*8)
		buf.Data[0] = 1
		txn.Commit()
	}

	{
		txn := jrnl.Begin()
		buf := txn.Read(a0, 4096*8)
		assert.Equal(byte(0), buf.Data[0])
	}
}

func TestAbortTxn(t *testing.T) {
	var d disk.Disk = disk.NewMemDisk(1000)
	jrnl := NewJrnl(&d)
	data := []byte{1, 2, 3, 4}
	a0 := mkAddr(513, 0)

	{
		txn := jrnl.Begin()
		bs := &bytes.Bytes{Data: data}
		txn.Write(a0, bs)
		txn.Abort()
	}

	{
		txn := jrnl.Begin()
		// after abort this shouldn't deadlock
		_ = txn.Read(a0, 4096*8)
		ok := txn.Commit()
		assert.True(t, ok, "read-only transaction should succeed")
	}
}
