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
	// this test is replicated as a Dafny method TestSubslice in machine.dfy
	bs := NewBytes(5)
	bs.Set(1, 3)
	bs.Set(2, 4)
	bs.Subslice(1, 3)
	assert.Equal(t, uint64(2), bs.Len())
	assert.Equal(t, byte(3), bs.Get(0))
	assert.Equal(t, byte(4), bs.Get(1))
}

func TestCopySegment(t *testing.T) {
	bs := NewBytes(5)
	bs.Set(2, 3)
	bs2 := NewBytes(3)
	bs2.Set(0, 1)
	bs2.Set(2, 2)

	bs2.CopySegment(1, bs, 2, 1)

	assert.Equal(t, []byte{0, 0, 3, 0, 0}, bs.Data)
	assert.Equal(t, []byte{1, 3, 2}, bs2.Data)
}

func TestCopySegmentAll(t *testing.T) {
	bs := NewBytes(3)
	bs.Data = []byte{1, 2, 3}

	bs2 := NewBytes(5)

	count := bs.Len()
	bs2.CopySegment(0, bs, 0, count)
	assert.Equal(t, []byte{1, 2, 3, 0, 0}, bs2.Data)
}

func TestCopySegmentClone(t *testing.T) {
	bs := &Bytes{Data: []byte{1, 2, 3}}

	count := bs.Len()
	bs2 := NewBytes(count)
	bs2.CopySegment(0, bs, 0, count)
	assert.Equal(t, bs.Data, bs2.Data)
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
