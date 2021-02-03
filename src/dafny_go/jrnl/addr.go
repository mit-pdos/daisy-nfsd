package jrnl

// manual definition of Addr datatype

type Addr_Addr struct {
	Blkno Blkno
	Off   uint64
}

type Addr struct {
	// note this is not exactly what Dafny would emit: it would put an interface
	// here which in practice is always the Addr_Addr struct
	Addr_Addr
}

type CompanionStruct_Addr_ struct{}

var Companion_Addr_ = CompanionStruct_Addr_{}

func (CompanionStruct_Addr_) Create_Addr_(blkno Blkno, off uint64) Addr {
	return Addr{Addr_Addr{blkno, off}}
}

func (_this Addr) Dtor_blkno() uint64 {
	return _this.Addr_Addr.Blkno
}

func (_this Addr) Dtor_off() uint64 {
	return _this.Addr_Addr.Off
}
