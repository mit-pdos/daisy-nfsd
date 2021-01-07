package compile_test

import (
	// TODO: this is an auto-generated name, which is really unfortunate. Dafny
	// master does not emit such an unpredictable name.
	bank "28_Bank_Compile_"
	"testing"

	"github.com/tchajed/goose/machine/disk"
)

func TestBankSanity(t *testing.T) {
	var d disk.Disk = disk.NewMemDisk(1000)
	b := bank.New_Bank_()
	b.Init(&d, 100)

	b.Transfer(0, 1)
	b.Transfer(0, 2)
	b.Transfer(1, 2)

	if !b.Audit() {
		t.Error("audit failed")
	}

	jrnl := b.Jrnl
	b = bank.New_Bank_()
	b.Recover(jrnl)
	if !b.Audit() {
		t.Error("audit failed")
	}
}
