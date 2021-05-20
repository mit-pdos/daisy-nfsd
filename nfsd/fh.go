package nfsd

import (
	"github.com/tchajed/marshal"

	"github.com/mit-pdos/go-nfsd/nfstypes"
)

type Fh struct {
	Ino uint64
}

func MakeFh(fh3 nfstypes.Nfs_fh3) Fh {
	dec := marshal.NewDec(fh3.Data)
	i := dec.GetInt()
	return Fh{Ino: i}
}

func (fh Fh) MakeFh3() nfstypes.Nfs_fh3 {
	enc := marshal.NewEnc(16)
	enc.PutInt(fh.Ino)
	fh3 := nfstypes.Nfs_fh3{Data: enc.Finish()}
	return fh3
}
