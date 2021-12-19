package encoding

import (
	"encoding/binary"

	"github.com/mit-pdos/daisy-nfsd/dafny_go/bytes"
)

func UInt64Put(x uint64, off uint64, bs *bytes.Bytes) {
	if bs.Invalid {
		panic("bytes invalid")
	}
	binary.LittleEndian.PutUint64(bs.Data[off:], x)
}

func UInt64Get(bs *bytes.Bytes, off uint64) uint64 {
	if bs.Invalid {
		panic("bytes invalid")
	}
	return binary.LittleEndian.Uint64(bs.Data[off:])
}

func UInt32Put(x uint32, off uint64, bs *bytes.Bytes) {
	if bs.Invalid {
		panic("bytes invalid")
	}
	binary.LittleEndian.PutUint32(bs.Data[off:], x)
}

func UInt32Get(bs *bytes.Bytes, off uint64) uint32 {
	if bs.Invalid {
		panic("bytes invalid")
	}
	return binary.LittleEndian.Uint32(bs.Data[off:])
}
