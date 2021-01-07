package jrnl

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func getArbitrary(m map[uint64]bool) uint64 {
	for x := range m {
		return x
	}
	return 0
}

func TestAllocator(t *testing.T) {
	assert := assert.New(t)

	used := make(map[uint64]bool)
	a := NewAllocator(100)
	a.MarkUsed(0)

	for i := 0; i < 20; i++ {
		x := a.Alloc()
		assert.LessOrEqual(x, uint64(100), "allocated out-of-range num")
		used[x] = true
	}
	for i := 0; i < 10; i++ {
		x := getArbitrary(used)
		a.Free(x)
	}

	for i := 0; i < 70; i++ {
		a.Alloc()
	}
}
