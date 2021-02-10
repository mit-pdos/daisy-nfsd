package compile_test

import (
	"testing"

	inode "Inode_Compile"
	_dafny "dafny"

	bytes "github.com/mit-pdos/dafny-jrnl/src/dafny_go/bytes"
	"github.com/stretchr/testify/assert"
	"github.com/tchajed/marshal"
)

func u64_slice_to_seq(xs []uint64) _dafny.Seq {
	xs_i := make([]interface{}, len(xs))
	for i, x := range xs {
		xs_i[i] = x
	}
	return _dafny.SeqOf(xs_i...)
}

func MkInode(sz uint64, blks []uint64) inode.Inode {
	blk_seq := u64_slice_to_seq(blks)
	return inode.Companion_Inode_.Create_Mk_(sz, blk_seq)
}

func EncodeIno(i inode.Inode) *bytes.Bytes {
	return inode.Companion_Default___.Encode__ino(i)
}

func DecodeIno(bs *bytes.Bytes) inode.Inode {
	return inode.Companion_Default___.Decode__ino(bs)
}

func decodeIno(bs []byte) (sz uint64, blks []uint64) {
	dec := marshal.NewDec(bs)
	sz = dec.GetInt()
	blks = make([]uint64, 15)
	for i := 0; i < 15; i++ {
		blks[i] = dec.GetInt()
	}
	return
}

func ManualDecodeIno(bs *bytes.Bytes) inode.Inode {
	sz, blks := decodeIno(bs.Data)
	return MkInode(sz, blks)
}

var i inode.Inode = MkInode(5000, []uint64{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15})

func BenchmarkInodeDecode(b *testing.B) {
	bs := EncodeIno(i)
	b.ResetTimer()
	for k := 0; k < b.N; k++ {
		DecodeIno(bs)
	}
}

func BenchmarkInodeDecodeManual(b *testing.B) {
	bs := EncodeIno(i)
	b.ResetTimer()
	for k := 0; k < b.N; k++ {
		ManualDecodeIno(bs)
	}
}

func TestDecodeIno(t *testing.T) {
	bs := EncodeIno(i).Data
	sz, blks := decodeIno(bs)
	assert.Equal(t, uint64(5000), sz, "size incorrect")
	assert.Equal(t, 15, len(blks), "len(blks) incorrect")
	assert.Equal(t, uint64(3), blks[2], "blks values incorrect")
}

func Benchmark_DecodeIno(b *testing.B) {
	bs := EncodeIno(i).Data
	b.ResetTimer()
	for k := 0; k < b.N; k++ {
		sz, blks := decodeIno(bs)
		if sz != 5000 || len(blks) != 15 {
			b.FailNow()
		}
	}
}
