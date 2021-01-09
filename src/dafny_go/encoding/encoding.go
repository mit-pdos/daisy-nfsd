package encoding

import (
	"encoding/binary"

	"github.com/mit-pdos/dafny-jrnl/src/dafny_go/bytes"
)

func UInt64Put(x uint64, off uint64, bs *bytes.Bytes) {
	binary.LittleEndian.PutUint64(bs.Data[off:], x)
}

func UInt64Get(bs *bytes.Bytes, off uint64) uint64 {
	return binary.LittleEndian.Uint64(bs.Data[off:])
}
