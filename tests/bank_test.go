package compile_test

import (
	"testing"

	bank "github.com/mit-pdos/daisy-nfsd/dafnygen/Bank_Compile"

	"github.com/stretchr/testify/assert"
	"github.com/tchajed/goose/machine/disk"
)

func TestBankSanity(t *testing.T) {
	assert := assert.New(t)
	var d disk.Disk = disk.NewMemDisk(1000)
	b := bank.New_Bank_()
	b.Init(&d, 100)

	b.Transfer(0, 1)
	b.Transfer(0, 2)
	b.Transfer(1, 2)

	jrnl := b.Jrnl
	b = bank.New_Bank_()
	b.Recover(jrnl)
	assert.Equal(uint64(98), b.Get(0))
	assert.Equal(uint64(102), b.Get(2))
}
