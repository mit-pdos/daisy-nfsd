package compile_test

import (
	// TODO: this is an auto-generated name, which is really unfortunate. Dafny
	// master does not emit such an unpredictable name.
	fs "47_Fs_Compile_"
	"testing"

	"github.com/mit-pdos/dafny-jrnl/src/dafny_go/bytes"

	"github.com/stretchr/testify/assert"
	"github.com/tchajed/goose/machine/disk"
)

func TestFsSanity(t *testing.T) {
	assert := assert.New(t)
	var d disk.Disk = disk.NewMemDisk(1000)
	filesys := fs.New_Filesys_()
	filesys.Init(&d)
	ino := uint64(3)

	bs := bytes.Data(make([]byte, 4096))
	copy(bs.Data, []byte{1, 2, 3, 4})
	filesys.Append(ino, bs)
	filesys.Append(ino, bs)
	bs2, ok := filesys.Get(ino, 4096, 4096)
	assert.True(ok)
	assert.Equal(byte(1), bs2.Data[0])
}
