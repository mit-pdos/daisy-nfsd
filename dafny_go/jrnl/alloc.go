package jrnl

import "github.com/mit-pdos/go-journal/alloc"

type Allocator struct {
	alloc alloc.Alloc
}

func NewAllocator(max uint64) *Allocator {
	a := alloc.MkMaxAlloc(max)
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

func (a *Allocator) NumFree() uint64 {
	return a.alloc.NumFree()
}
