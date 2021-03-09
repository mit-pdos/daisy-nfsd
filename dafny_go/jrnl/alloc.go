package jrnl

import "github.com/mit-pdos/goose-nfsd/alloc"

type Allocator struct {
	alloc alloc.Alloc
}

func NewAllocator(max uint64) *Allocator {
	if !(0 < max && max%8 == 0) {
		panic("invalid max, must be at least 0 and divisible by 8")
	}
	num_bytes := max / 8
	a := alloc.MkAlloc(make([]byte, num_bytes))
	a.MarkUsed(0)
	return &Allocator{alloc: *a}
}

func (a *Allocator) MarkUsed(x uint64) {
	a.alloc.MarkUsed(x)
}

func (a *Allocator) Alloc() uint64 {
	return a.alloc.AllocNum()
}

func (a *Allocator) Free(x uint64) {
	a.alloc.FreeNum(x)
}
