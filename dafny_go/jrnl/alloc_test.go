package jrnl

import "testing"

func getArbitrary(m map[uint64]bool) uint64 {
	for x := range m {
		return x
	}
	return 0
}

func TestAllocator(t *testing.T) {
	// the allocator has no preconditions so we just attempt to exercise it a bit
	used := make(map[uint64]bool)
	a := NewAllocator(128)

	for i := 0; i < 20; i++ {
		x := a.Alloc()
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
