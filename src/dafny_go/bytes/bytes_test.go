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
