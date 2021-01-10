package jrnl

import "github.com/mit-pdos/goose-nfsd/alloc"

type Allocator struct {
	alloc alloc.Alloc
}

func NewAllocator(max uint64) *Allocator {
	if max == 0 {
		panic("invalid max, must be at least 0")
	}
	num_bytes := max / 8
	a := alloc.MkAlloc(make([]byte, num_bytes))
	return &Allocator{alloc: *a}
}

func (a *Allocator) MarkUsed(x uint64) {
	a.alloc.MarkUsed(x)
}

func (a *Allocator) Alloc() uint64 {
	return a.alloc.AllocNum()
}

func (a *Allocator) Free(x uint64) {
	// avoid panic in alloc implementation
	if x == 0 {
		return
	}
	a.alloc.FreeNum(x)
}
