package nfsd

import (
	"fmt"

	direntries "github.com/mit-pdos/dafny-jrnl/dafnygen/DirEntries_Compile"
	dirfs "github.com/mit-pdos/dafny-jrnl/dafnygen/DirFs_Compile"
	inode "github.com/mit-pdos/dafny-jrnl/dafnygen/Inode_Compile"
	dafny "github.com/mit-pdos/dafny-jrnl/dafnygen/dafny"

	"github.com/mit-pdos/dafny-jrnl/dafny_go/bytes"

	"github.com/mit-pdos/goose-nfsd/nfstypes"
	"github.com/mit-pdos/goose-nfsd/util"
)

var _ = fmt.Printf

func fh2ino(fh3 nfstypes.Nfs_fh3) uint64 {
	fh := MakeFh(fh3)
	return fh.Ino
}

func (nfs *Nfs) NFSPROC3_NULL() {
	util.DPrintf(0, "NFS Null\n")
}

func (nfs *Nfs) NFSPROC3_GETATTR(args nfstypes.GETATTR3args) nfstypes.GETATTR3res {
	var reply nfstypes.GETATTR3res
	util.DPrintf(1, "NFS GetAttr %v\n", args)

	txn := nfs.filesys.Begin()
	inum := fh2ino(args.Object)

	ok, stat := nfs.filesys.GETATTR(txn, inum)
	if ok {
		ok = txn.Commit()
	} else {
		txn.Abort()
	}

	if ok {
		attrs := stat.Get().(dirfs.Attributes_Attributes)
		if attrs.Is__dir {
			reply.Resok.Obj_attributes.Ftype = nfstypes.NF3DIR
		} else {
			reply.Resok.Obj_attributes.Ftype = nfstypes.NF3REG
		}
		reply.Resok.Obj_attributes.Mode = 0777
		reply.Resok.Obj_attributes.Nlink = 1
		reply.Resok.Obj_attributes.Size = nfstypes.Size3(attrs.Size)
		reply.Resok.Obj_attributes.Fileid = nfstypes.Fileid3(inum)
		reply.Status = nfstypes.NFS3_OK
	} else {
		reply.Status = nfstypes.NFS3ERR_SERVERFAULT
	}

	return reply
}

func (nfs *Nfs) NFSPROC3_SETATTR(args nfstypes.SETATTR3args) nfstypes.SETATTR3res {
	var reply nfstypes.SETATTR3res
	util.DPrintf(1, "NFS SetAttr %v\n", args)

	reply.Status = nfstypes.NFS3ERR_NOTSUPP
	return reply
}

// Lookup must lock child inode to find gen number
func (nfs *Nfs) NFSPROC3_LOOKUP(args nfstypes.LOOKUP3args) nfstypes.LOOKUP3res {
	util.DPrintf(1, "NFS Lookup %v\n", args)
	var reply nfstypes.LOOKUP3res

	txn := nfs.filesys.Begin()
	inum := fh2ino(args.What.Dir)
	name := seqOfString(args.What.Name)

	err, found, f_ino := nfs.filesys.Lookup(txn, inum, name)
	if !err.Is_NoError() {
		txn.Abort()
		reply.Status = nfstypes.NFS3ERR_SERVERFAULT
		return reply
	}
	if !found {
		txn.Commit()
		reply.Status = nfstypes.NFS3ERR_NOENT
		return reply
	}
	fh := Fh{Ino: f_ino}
	reply.Resok.Object = fh.MakeFh3()
	reply.Status = nfstypes.NFS3_OK
	txn.Commit()
	return reply
}

func (nfs *Nfs) NFSPROC3_ACCESS(args nfstypes.ACCESS3args) nfstypes.ACCESS3res {
	util.DPrintf(1, "NFS Access %v\n", args)
	var reply nfstypes.ACCESS3res
	reply.Status = nfstypes.NFS3_OK
	reply.Resok.Access = nfstypes.Uint32(nfstypes.ACCESS3_READ | nfstypes.ACCESS3_LOOKUP | nfstypes.ACCESS3_MODIFY | nfstypes.ACCESS3_EXTEND | nfstypes.ACCESS3_DELETE | nfstypes.ACCESS3_EXECUTE)
	return reply
}

func (nfs *Nfs) NFSPROC3_READ(args nfstypes.READ3args) nfstypes.READ3res {
	var reply nfstypes.READ3res
	util.DPrintf(1, "NFS Read %v %d %d\n", args.File, args.Offset, args.Count)

	txn := nfs.filesys.Begin()
	inum := fh2ino(args.File)

	// args.Offset
	// args.Count
	err, bs := nfs.filesys.Read(txn, inum, uint64(args.Offset), uint64(args.Count))
	if !err.Is_NoError() {
		reply.Status = nfstypes.NFS3ERR_NOTSUPP
		txn.Abort()
		return reply
	}

	reply.Resok.Count = nfstypes.Count3(bs.Len())
	reply.Resok.Data = bs.Data
	reply.Resok.Eof = false
	reply.Status = nfstypes.NFS3_OK
	txn.Commit()
	return reply
}

func (nfs *Nfs) NFSPROC3_WRITE(args nfstypes.WRITE3args) nfstypes.WRITE3res {
	var reply nfstypes.WRITE3res
	util.DPrintf(1, "NFS Write %v off %d cnt %d how %d\n", args.File, args.Offset,
		args.Count, args.Stable)

	txn := nfs.filesys.Begin()
	inum := fh2ino(args.File)

	// XXX write at offset args.Offset

	bs := bytes.Data(args.Data)
	err := nfs.filesys.Append(txn, inum, bs)
	if !err.Is_NoError() {
		reply.Status = nfstypes.NFS3ERR_NOTSUPP
		txn.Abort()
		return reply
	}

	reply.Resok.Count = args.Count
	reply.Resok.Committed = nfstypes.FILE_SYNC
	reply.Status = nfstypes.NFS3_OK
	txn.Commit()
	return reply
}

func seqOfString(name nfstypes.Filename3) dafny.Seq {
	var namebytes []interface{}
	for _, ch := range name {
		namebytes = append(namebytes, uint8(ch))
	}
	// TODO: SeqOf makes a defensive copy, we should use a lower-level constructor
	return dafny.SeqOf(namebytes...)
}

func stringOfSeq(s dafny.Seq) string {
	numbytes := s.LenInt()
	bs := make([]byte, numbytes)
	for i := 0; i < numbytes; i++ {
		bs[i] = s.IndexInt(i).(uint8)
	}
	return string(bs)
}

func (nfs *Nfs) NFSPROC3_CREATE(args nfstypes.CREATE3args) nfstypes.CREATE3res {
	util.DPrintf(1, "NFS Create %v\n", args)
	var reply nfstypes.CREATE3res

	txn := nfs.filesys.Begin()
	inum := fh2ino(args.Where.Dir)

	nameseq := seqOfString(args.Where.Name)
	ok, finum := nfs.filesys.CreateFile(txn, inum, nameseq)
	if !ok {
		reply.Status = nfstypes.NFS3ERR_NOTSUPP
		txn.Abort()
		return reply
	}

	// XXX set size based on args.How.Obj_attributes.Size

	txn.Commit()
	reply.Status = nfstypes.NFS3_OK
	reply.Resok.Obj.Handle_follows = true
	reply.Resok.Obj.Handle = Fh{Ino: finum}.MakeFh3()
	return reply
}

func (nfs *Nfs) NFSPROC3_MKDIR(args nfstypes.MKDIR3args) nfstypes.MKDIR3res {
	util.DPrintf(1, "NFS Mkdir %v\n", args)
	var reply nfstypes.MKDIR3res

	txn := nfs.filesys.Begin()
	inum := fh2ino(args.Where.Dir)

	nameseq := seqOfString(args.Where.Name)
	ok, finum := nfs.filesys.CreateDir(txn, inum, nameseq)
	if !ok {
		reply.Status = nfstypes.NFS3ERR_NOTSUPP
		txn.Abort()
		return reply
	}

	txn.Commit()
	reply.Status = nfstypes.NFS3_OK
	reply.Resok.Obj.Handle_follows = true
	reply.Resok.Obj.Handle = Fh{Ino: finum}.MakeFh3()
	return reply
}

func (nfs *Nfs) NFSPROC3_SYMLINK(args nfstypes.SYMLINK3args) nfstypes.SYMLINK3res {
	util.DPrintf(1, "NFS Symlink %v\n", args)
	var reply nfstypes.SYMLINK3res
	reply.Status = nfstypes.NFS3ERR_NOTSUPP
	return reply
}

func (nfs *Nfs) NFSPROC3_READLINK(args nfstypes.READLINK3args) nfstypes.READLINK3res {
	util.DPrintf(1, "NFS Readlink %v\n", args)
	var reply nfstypes.READLINK3res
	reply.Status = nfstypes.NFS3ERR_NOTSUPP
	return reply
}

func (nfs *Nfs) NFSPROC3_MKNOD(args nfstypes.MKNOD3args) nfstypes.MKNOD3res {
	util.DPrintf(1, "NFS Mknod %v\n", args)
	var reply nfstypes.MKNOD3res
	reply.Status = nfstypes.NFS3ERR_NOTSUPP
	return reply
}

func (nfs *Nfs) NFSPROC3_REMOVE(args nfstypes.REMOVE3args) nfstypes.REMOVE3res {
	util.DPrintf(1, "NFS Remove %v\n", args)
	var reply nfstypes.REMOVE3res

	txn := nfs.filesys.Begin()
	inum := fh2ino(args.Object.Dir)
	name := seqOfString(args.Object.Name)
	err := nfs.filesys.Unlink(txn, inum, name)
	if !err.Is_NoError() {
		// XXX do better job conveying errors, EINVAL for !dir
		reply.Status = nfstypes.NFS3ERR_NOENT
		txn.Abort()
		return reply
	}
	reply.Status = nfstypes.NFS3_OK
	txn.Commit()
	return reply
}

func (nfs *Nfs) NFSPROC3_RMDIR(args nfstypes.RMDIR3args) nfstypes.RMDIR3res {
	util.DPrintf(1, "NFS Rmdir %v\n", args)
	var reply nfstypes.RMDIR3res
	reply.Status = nfstypes.NFS3ERR_NOTSUPP
	return reply
}

func (nfs *Nfs) NFSPROC3_RENAME(args nfstypes.RENAME3args) nfstypes.RENAME3res {
	util.DPrintf(1, "NFS Rename %v\n", args)
	var reply nfstypes.RENAME3res
	reply.Status = nfstypes.NFS3ERR_NOTSUPP
	return reply
}

func (nfs *Nfs) NFSPROC3_LINK(args nfstypes.LINK3args) nfstypes.LINK3res {
	util.DPrintf(1, "NFS Link %v\n", args)
	var reply nfstypes.LINK3res
	reply.Status = nfstypes.NFS3ERR_NOTSUPP
	return reply
}

func (nfs *Nfs) NFSPROC3_READDIR(args nfstypes.READDIR3args) nfstypes.READDIR3res {
	util.DPrintf(1, "NFS Readdir %v\n", args)
	var reply nfstypes.READDIR3res

	txn := nfs.filesys.Begin()
	inum := fh2ino(args.Dir)

	err, seq := nfs.filesys.Readdir(txn, inum)
	if !err.Is_NoError() {
		txn.Abort()
		reply.Status = nfstypes.NFS3ERR_SERVERFAULT
		return reply
	}

	seqlen := seq.LenInt()
	var ents *nfstypes.Entry3
	for i := 0; i < seqlen; i++ {
		dirent := seq.IndexInt(i).(direntries.DirEnt)
		dirent2 := dirent.Get().(direntries.DirEnt_DirEnt)

		de_ino := dirent2.Ino
		de_name := stringOfSeq(dirent2.Name)

		ents = &nfstypes.Entry3{
			Fileid:    nfstypes.Fileid3(de_ino),
			Name:      nfstypes.Filename3(de_name),
			Cookie:    nfstypes.Cookie3(i + 1),
			Nextentry: ents,
		}
	}

	txn.Commit()
	reply.Status = nfstypes.NFS3_OK
	reply.Resok.Reply = nfstypes.Dirlist3{Entries: ents, Eof: true}
	return reply
}

func (nfs *Nfs) NFSPROC3_READDIRPLUS(args nfstypes.READDIRPLUS3args) nfstypes.READDIRPLUS3res {
	util.DPrintf(1, "NFS Readdirplus %v\n", args)
	var reply nfstypes.READDIRPLUS3res
	reply.Status = nfstypes.NFS3ERR_NOTSUPP
	return reply
}

func (nfs *Nfs) NFSPROC3_FSSTAT(args nfstypes.FSSTAT3args) nfstypes.FSSTAT3res {
	util.DPrintf(1, "NFS Fsstat %v\n", args)
	var reply nfstypes.FSSTAT3res
	reply.Status = nfstypes.NFS3_OK
	reply.Resok.Obj_attributes.Attributes_follow = false
	return reply
}

func (nfs *Nfs) NFSPROC3_FSINFO(args nfstypes.FSINFO3args) nfstypes.FSINFO3res {
	util.DPrintf(1, "NFS Fsinfo %v\n", args)
	var reply nfstypes.FSINFO3res
	reply.Status = nfstypes.NFS3_OK
	reply.Resok.Rtmax = nfstypes.Uint32(4096)
	reply.Resok.Rtpref = reply.Resok.Rtmax
	reply.Resok.Wtmax = nfstypes.Uint32(4096)
	reply.Resok.Wtpref = reply.Resok.Wtmax
	reply.Resok.Maxfilesize = nfstypes.Size3(inode.Companion_Default___.MAX__SZ__u64())
	reply.Resok.Dtpref = 128
	reply.Resok.Properties = nfstypes.Uint32(nfstypes.FSF3_HOMOGENEOUS)
	return reply
}

func (nfs *Nfs) NFSPROC3_PATHCONF(args nfstypes.PATHCONF3args) nfstypes.PATHCONF3res {
	util.DPrintf(1, "NFS Pathconf %v\n", args)
	var reply nfstypes.PATHCONF3res
	// TODO: should return name_max here (to 24, which is
	// DirEntries.MAX_FILENAME_SZ)
	reply.Status = nfstypes.NFS3ERR_NOTSUPP
	return reply
}

func (nfs *Nfs) NFSPROC3_COMMIT(args nfstypes.COMMIT3args) nfstypes.COMMIT3res {
	util.DPrintf(1, "NFS Commit %v\n", args)
	var reply nfstypes.COMMIT3res

	reply.Status = nfstypes.NFS3_OK
	return reply
}
