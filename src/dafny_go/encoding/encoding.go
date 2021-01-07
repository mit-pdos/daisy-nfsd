package encoding

import (
	"github.com/mit-pdos/dafny-jrnl/src/dafny_go/bytes"
	"github.com/tchajed/goose/machine"
)

func UInt64Put(x uint64, off uint64, bs *bytes.Bytes) {
	machine.UInt64Put(bs.Data[off:], x)
}

func UInt64Get(bs *bytes.Bytes, off uint64) uint64 {
	return machine.UInt64Get(bs.Data[off:])
}
