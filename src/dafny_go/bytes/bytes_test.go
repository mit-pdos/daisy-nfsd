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
