package bytes

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestBytes(t *testing.T) {
	bs := NewBytes(1)
	bs.Append(1)
	assert.Equal(t, byte(0), bs.Get(0))
	assert.Equal(t, byte(1), bs.Get(1))
}

func TestAppend(t *testing.T) {
	bs := NewBytes(1)
	bs2 := NewBytes(3)
	bs.AppendBytes(bs2)
	assert.Equal(t, uint64(4), bs.Len())
}

func TestSubslice(t *testing.T) {
	// this test is replicated as a Dafny method TestSubslice in machine.s.dfy
	bs := NewBytes(5)
	bs.Set(1, 3)
	bs.Set(2, 4)
	bs.Subslice(1, 3)
	assert.Equal(t, uint64(2), bs.Len())
	assert.Equal(t, byte(3), bs.Get(0))
	assert.Equal(t, byte(4), bs.Get(1))
}

func TestCopyTo(t *testing.T) {
	bs := NewBytes(3)
	bs2 := NewBytes(2)
	bs2.Data[1] = byte(4)
	assert.Equal(t, []byte{0, 4}, bs2.Data)

	bs.CopyTo(1, bs2)
	assert.Equal(t, uint64(3), bs.Len())
	assert.Equal(t, byte(0), bs.Get(0))
	assert.Equal(t, byte(4), bs.Get(2))

	assert.Equal(t, []byte{0, 4}, bs2.Data)
}

func TestCopyFrom(t *testing.T) {
	bs := NewBytes(5)
	bs.Set(2, 3)
	bs2 := NewBytes(2)
	bs2.CopyFrom(bs, 2, 1)
	assert.Equal(t, byte(3), bs2.Get(0))
}

func TestSplit(t *testing.T) {
	bs := NewBytes(3)
	bs.Data[1] = 1
	bs2 := bs.Split(1)

	assert.Equal(t, uint64(1), bs.Len())
	assert.Equal(t, uint64(2), bs2.Len())

	assert.Equal(t, []byte{0}, bs.Data)
	assert.Equal(t, []byte{1, 0}, bs2.Data)

	bs.Append(2)
	assert.Equal(t, byte(2), bs.Get(1), "we just wrote that")
	assert.Equal(t, byte(1), bs2.Get(0), "Split did not create independent slice")
}
