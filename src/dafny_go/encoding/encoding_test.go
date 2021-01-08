package encoding

import (
	"testing"

	"github.com/mit-pdos/dafny-jrnl/src/dafny_go/bytes"
	"github.com/stretchr/testify/assert"
)

func TestEncodeOf0(t *testing.T) {
	bs := bytes.NewBytes(8)
	for i := 0; i < 8; i++ {
		bs.Data[i] = 1
	}

	UInt64Put(0, 0, bs)

	assert.Equal(t, []byte{0, 0, 0, 0, 0, 0, 0, 0}, bs.Data[:8],
		"encoding of zero is not 8 zeros")
}

func TestEncodeDecodeAt0(t *testing.T) {
	assert := assert.New(t)
	for _, x := range []uint64{
		0, 1,
		0xFFFF_FFFF_FFFF_FFFF,
		0x0102_0304_0506_0708,
	} {
		bs := bytes.NewBytes(8)
		UInt64Put(x, 0, bs)
		assert.Equal(x, UInt64Get(bs, 0))
	}
}

func TestEncodeDecodeOffset(t *testing.T) {
	assert := assert.New(t)
	var x uint64 = 0x0102_0304_0506_0708
	bs := bytes.NewBytes(16)
	UInt64Put(x, 4, bs)
	assert.Equal(x, UInt64Get(bs, 4))

	bs = bytes.NewBytes(4 + 8)
	UInt64Put(x, 4, bs)
	assert.Equal(x, UInt64Get(bs, 4))
}
