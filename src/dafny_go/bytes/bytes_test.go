package bytes

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestBytes(t *testing.T) {
	assert := assert.New(t)
	bs := NewBytes(1)
	bs.Append(1)
	assert.Equal(byte(0), bs.Get(0))
	assert.Equal(byte(1), bs.Get(1))
}

func TestAppend(t *testing.T) {
	assert := assert.New(t)
	bs := NewBytes(1)
	bs2 := NewBytes(3)
	bs.AppendBytes(bs2)
	assert.Equal(uint64(4), bs.Len())
}
