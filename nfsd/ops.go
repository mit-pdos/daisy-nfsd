package nfsd

import (
	"fmt"
	"time"

	direntries "github.com/mit-pdos/daisy-nfsd/dafnygen/DirEntries"
	dirfs "github.com/mit-pdos/daisy-nfsd/dafnygen/DirFs"
	inode "github.com/mit-pdos/daisy-nfsd/dafnygen/Inode"
	lock_order "github.com/mit-pdos/daisy-nfsd/dafnygen/LockOrder"
	memdirents "github.com/mit-pdos/daisy-nfsd/dafnygen/MemDirEnts"
	dafny_nfs "github.com/mit-pdos/daisy-nfsd/dafnygen/Nfs"
	nfs_spec "github.com/mit-pdos/daisy-nfsd/dafnygen/Nfs"
	std "github.com/mit-pdos/daisy-nfsd/dafnygen/Std"
	typed_fs "github.com/mit-pdos/daisy-nfsd/dafnygen/TypedFs"
	dafny "github.com/mit-pdos/daisy-nfsd/dafnygen/dafny"

	"github.com/mit-pdos/daisy-nfsd/dafny_go/bytes"
	"github.com/mit-pdos/daisy-nfsd/dafny_go/jrnl"

	"github.com/mit-pdos/go-journal/util"
	"github.com/mit-pdos/go-nfsd/nfstypes"
)

var _ = fmt.Printf

func fh2ino(fh3 nfstypes.Nfs_fh3) uint64 {
	// avoid panic on invalid file handles
	if len(fh3.Data) != 16 {
		return 0
	}
	fh := MakeFh(fh3)
	return fh.Ino
}

func optionFromBool(set_it bool, x interface{}) std.Option {
	if set_it {
		return std.Companion_Option_.Create_Some_(x)
	}
	return std.Companion_Option_.Create_None_()
}

func encodeTime(time nfstypes.Nfstime3) inode.NfsTime {
	return inode.Companion_NfsTime_.Create_NfsTime_(uint32(time.Seconds), uint32(time.Nseconds))
}

func decodeTime(time inode.NfsTime) nfstypes.Nfstime3 {
	return nfstypes.Nfstime3{
		Seconds:  nfstypes.Uint32(time.Dtor_sec()),
		Nseconds: nfstypes.Uint32(time.Dtor_nsec()),
	}
}

func encodeSetTime(how nfstypes.Time_how, time nfstypes.Nfstime3) nfs_spec.SetTime {
	if how == nfstypes.DONT_CHANGE {
		return nfs_spec.Companion_SetTime_.Create_DontChange_()
	}
	if how == nfstypes.SET_TO_SERVER_TIME {
		return nfs_spec.Companion_SetTime_.Create_SetToServerTime_()
	}
	if how == nfstypes.SET_TO_CLIENT_TIME {
		return nfs_spec.Companion_SetTime_.Create_SetToClientTime_(encodeTime(time))
	}
	util.DPrintf(2, "unexpected time_how %d", how)
	return nfs_spec.Companion_SetTime_.Create_DontChange_()
}

func encodeSattr3(attrs nfstypes.Sattr3) nfs_spec.Sattr3 {
	mode := optionFromBool(attrs.Mode.Set_it, uint32(attrs.Mode.Mode))
	uid := optionFromBool(attrs.Uid.Set_it, uint32(attrs.Uid.Uid))
	gid := optionFromBool(attrs.Gid.Set_it, uint32(attrs.Gid.Gid))
	size := optionFromBool(attrs.Size.Set_it, uint64(attrs.Size.Size))
	atime := encodeSetTime(attrs.Atime.Set_it, attrs.Atime.Atime)
	mtime := encodeSetTime(attrs.Mtime.Set_it, attrs.Mtime.Mtime)
	return nfs_spec.Companion_Sattr3_.Create_Sattr3_(
		mode,
		uid, gid,
		size,
		atime, mtime,
	)
}

func encodeCreateHow(how nfstypes.Createhow3) nfs_spec.CreateHow3 {
	if how.Mode == nfstypes.UNCHECKED {
		return nfs_spec.Companion_CreateHow3_.Create_Unchecked_(encodeSattr3(how.Obj_attributes))
	}
	if how.Mode == nfstypes.GUARDED {
		return nfs_spec.Companion_CreateHow3_.Create_Guarded_(encodeSattr3(how.Obj_attributes))
	}
	if how.Mode == nfstypes.EXCLUSIVE {
		t := inode.Companion_NfsTime_.Decode(&bytes.Bytes{Data: how.Verf[:]}, 0)
		return nfs_spec.Companion_CreateHow3_.Create_Exclusive_(t)
	}
	util.DPrintf(2, "unexpected createhow3 %d", how.Mode)
	// construct a dummy createhow3
	return nfs_spec.Companion_CreateHow3_.Create_Unchecked_(
		encodeSattr3(nfstypes.Sattr3{}))
}

func decodeAttrs(attrs inode.Attrs, fattr *nfstypes.Fattr3) {
	fattr.Mode = nfstypes.Mode3(attrs.Dtor_mode())
	fattr.Uid = nfstypes.Uid3(attrs.Dtor_uid())
	fattr.Gid = nfstypes.Gid3(attrs.Dtor_gid())
	fattr.Mtime = decodeTime(attrs.Dtor_mtime())
	fattr.Ctime = decodeTime(attrs.Dtor_mtime())
}

func decodeFattr3(attrs nfs_spec.Fattr3, inum uint64, fattr *nfstypes.Fattr3) {
	decodeAttrs(attrs.Dtor_attrs(), fattr)
	fattr.Ftype = nfstypes.Ftype3(attrs.Dtor_ftype().To__uint32())
	fattr.Nlink = 1
	fattr.Size = nfstypes.Size3(attrs.Dtor_size())
	fattr.Used = nfstypes.Size3(attrs.Dtor_size())
	fattr.Fileid = nfstypes.Fileid3(inum)
	fattr.Fsid = 123
}

// extract wcc.before data
func decodeBefore(attrs nfs_spec.BeforeAttr, fattr *nfstypes.Wcc_attr) {
	fattr.Size = nfstypes.Size3(attrs.Dtor_size())
	fattr.Mtime = decodeTime(attrs.Dtor_mtime())
	fattr.Ctime = decodeTime(attrs.Dtor_mtime())
}

func decodeFsstat3(stats nfs_spec.Fsstat3, fsstat *nfstypes.FSSTAT3res) {
	fsstat.Resok.Tbytes = nfstypes.Size3(stats.Dtor_tbytes())
	fsstat.Resok.Fbytes = nfstypes.Size3(stats.Dtor_fbytes())
	fsstat.Resok.Abytes = nfstypes.Size3(stats.Dtor_fbytes())
	fsstat.Resok.Tfiles = nfstypes.Size3(stats.Dtor_tfiles())
	fsstat.Resok.Ffiles = nfstypes.Size3(stats.Dtor_ffiles())
	fsstat.Resok.Afiles = nfstypes.Size3(stats.Dtor_ffiles())
}

func (nfs *Nfs) NFSPROC3_NULL() {
	util.DPrintf(1, "NFS Null\n")
}

type Txn = *jrnl.Txn
type Result = dafny_nfs.Result

func parseResult(r Result) (v interface{}, status nfstypes.Nfsstat3, hint uint64) {
	if r.Is_Ok() {
		v = r.Dtor_v()
	} else {
		if r.Dtor_err().Is_JukeBox() {
			hint = r.Dtor_err().Dtor_sz__hint()
		}
	}
	status = nfstypes.Nfsstat3(r.Err__code())
	return
}

func (nfs *Nfs) runTxn(f func(txn Txn) Result) (v interface{}, status nfstypes.Nfsstat3, hint uint64) {
	txn := nfs.filesys.Begin()
	r := f(txn)
	r = dirfs.Companion_Default___.HandleResult(r, txn, true)
	v, status, hint = parseResult(r)
	return
}

func (nfs *Nfs) ZeroFreeSpace(inum uint64, szHint uint64) {
	if szHint == 0 {
		return
	}
	util.DPrintf(1, "ZeroFreeSpace: freeing %v up to %v\n", inum, szHint)
	for {
		v, _, _ := nfs.runTxn(func(txn Txn) Result {
			return nfs.filesys.ZeroFreeSpace(txn, inum, szHint)
		})
		done := v.(bool)
		if done {
			return
		}
		util.DPrintf(2, "ZeroFreeSpace: freeing %v again\n", inum)
	}
}

func filenameToBytes(name nfstypes.Filename3) *bytes.Bytes {
	return &bytes.Bytes{Data: []byte(name)}
}

func (nfs *Nfs) NFSPROC3_GETATTR(args nfstypes.GETATTR3args) (reply nfstypes.GETATTR3res) {
	util.DPrintf(1, "NFS GetAttr %v\n", args)
	defer nfs.reportOp(nfstypes.NFSPROC3_GETATTR, time.Now())

	inum := fh2ino(args.Object)

	stat, status, _ := nfs.runTxn(func(txn Txn) Result {
		return nfs.filesys.GETATTR(txn, inum)
	})
	reply.Status = status
	if status != nfstypes.NFS3_OK {
		util.DPrintf(2, "NFS Getattr error %v", status)
		return reply
	}

	attrs := stat.(nfs_spec.Fattr3)
	decodeFattr3(attrs, inum, &reply.Resok.Obj_attributes)

	return reply
}

func (nfs *Nfs) NFSPROC3_SETATTR(args nfstypes.SETATTR3args) (reply nfstypes.SETATTR3res) {
	util.DPrintf(1, "NFS SetAttr %v\n", args)
	defer nfs.reportOp(nfstypes.NFSPROC3_SETATTR, time.Now())
	if args.Guard.Check {
		reply.Status = nfstypes.NFS3ERR_NOTSUPP
		return reply
	}
	inum := fh2ino(args.Object)
	sattr := encodeSattr3(args.New_attributes)

	_, status, hint := nfs.runTxn(func(txn Txn) Result {
		return nfs.filesys.SETATTR(txn, inum, sattr)
	})
	if status == nfstypes.NFS3ERR_JUKEBOX {
		go nfs.ZeroFreeSpace(inum, hint)
	}
	if status != nfstypes.NFS3_OK {
		util.DPrintf(2, "NFS Setattr error %v", status)
		return reply
	}
	reply.Status = status

	return reply
}

func (nfs *Nfs) NFSPROC3_LOOKUP(args nfstypes.LOOKUP3args) (reply nfstypes.LOOKUP3res) {
	util.DPrintf(1, "NFS Lookup %v\n", args)
	defer nfs.reportOp(nfstypes.NFSPROC3_LOOKUP, time.Now())

	inum := fh2ino(args.What.Dir)
	name := filenameToBytes(args.What.Name)

	var dattr std.Option
	r, status, _ := nfs.runTxn(func(txn Txn) Result {
		var r Result
		r, dattr = nfs.filesys.LOOKUP(txn, inum, name)
		return r
	})
	reply.Status = status
	if status != nfstypes.NFS3_OK {
		util.DPrintf(2, "NFS Lookup error %v", status)
		if dattr.Is_Some() {
			reply.Resfail.Dir_attributes.Attributes_follow = true
			decodeFattr3(dattr.Dtor_x().(nfs_spec.Fattr3),
				inum, &reply.Resfail.Dir_attributes.Attributes)
		}
		return reply
	}
	ino_r := r.(nfs_spec.InoResult)
	ino := ino_r.Dtor_ino()
	fh := Fh{Ino: ino}
	reply.Resok.Object = fh.MakeFh3()
	reply.Resok.Obj_attributes.Attributes_follow = true
	decodeFattr3(ino_r.Dtor_attrs(), ino, &reply.Resok.Obj_attributes.Attributes)
	if dattr.Is_Some() {
		reply.Resok.Dir_attributes.Attributes_follow = true
		decodeFattr3(dattr.Dtor_x().(nfs_spec.Fattr3),
			inum, &reply.Resok.Dir_attributes.Attributes)
	}
	return reply
}

func (nfs *Nfs) NFSPROC3_ACCESS(args nfstypes.ACCESS3args) (reply nfstypes.ACCESS3res) {
	util.DPrintf(1, "NFS Access %v\n", args)
	defer nfs.reportOp(nfstypes.NFSPROC3_ACCESS, time.Now())
	reply.Status = nfstypes.NFS3_OK

	// run a transaction just to get the post-op attributes
	/*
		inum := fh2ino(args.Object)

		stat, status, _ := nfs.runTxn(func(txn Txn) Result {
			return nfs.filesys.GETATTR(txn, inum)
		})
		reply.Status = status
		if status != nfstypes.NFS3_OK {
			util.DPrintf(2, "NFS Access error %v", status)
			return reply
		}

		attrs := stat.(nfs_spec.Fattr3)
		reply.Resok.Obj_attributes.Attributes_follow = true
		decodeFattr3(attrs, inum, &reply.Resok.Obj_attributes.Attributes)
	*/

	reply.Resok.Access = nfstypes.Uint32(nfstypes.ACCESS3_READ | nfstypes.ACCESS3_LOOKUP | nfstypes.ACCESS3_MODIFY | nfstypes.ACCESS3_EXTEND | nfstypes.ACCESS3_DELETE | nfstypes.ACCESS3_EXECUTE)
	return reply
}

func (nfs *Nfs) NFSPROC3_READ(args nfstypes.READ3args) (reply nfstypes.READ3res) {
	util.DPrintf(1, "NFS Read %v %d %d\n", args.File, args.Offset, args.Count)
	defer nfs.reportOp(nfstypes.NFSPROC3_READ, time.Now())

	inum := fh2ino(args.File)
	off := uint64(args.Offset)
	count := uint64(args.Count)

	r, status, _ := nfs.runTxn(func(txn Txn) Result {
		return nfs.filesys.READ(txn, inum, off, count)
	})
	reply.Status = status
	if status != nfstypes.NFS3_OK {
		util.DPrintf(1, "NFS Read error %v", status)
		return reply
	}
	rr := r.(nfs_spec.ReadResult)
	bs := rr.Dtor_data()
	eof := rr.Dtor_eof()

	reply.Resok.Count = nfstypes.Count3(bs.Len())
	reply.Resok.Data = bs.Data
	reply.Resok.Eof = eof
	return reply
}

func (nfs *Nfs) NFSPROC3_WRITE(args nfstypes.WRITE3args) (reply nfstypes.WRITE3res) {
	util.DPrintf(1, "NFS Write %v off %d cnt %d how %d\n", args.File, args.Offset,
		args.Count, args.Stable)
	defer nfs.reportOp(nfstypes.NFSPROC3_WRITE, time.Now())

	inum := fh2ino(args.File)
	off := uint64(args.Offset)
	cnt := uint64(args.Count)
	if cnt > uint64(len(args.Data)) {
		cnt = uint64(len(args.Data))
	}

	// copy args.Data[:cnt] since RPC library can re-use the input buffer and we
	// need to give ownership to Dafny (and eventually to GoTxn)
	bs := bytes.NewBytes(cnt)
	copy(bs.Data, args.Data)

	// (v interface{}, status nfstypes.Nfsstat3, hint uint64

	var (
		r      interface{}
		status nfstypes.Nfsstat3
		hint   uint64
	)
	unstable := args.Stable == nfstypes.UNSTABLE && nfs.asyncWrites
	if unstable {
		txn := nfs.filesys.Begin()
		res := nfs.filesys.WRITE(txn, inum, off, bs)
		// NOTE: pass wait=false, which is unverified
		res = dirfs.Companion_Default___.HandleResult(res, txn, false)
		r, status, hint = parseResult(res)
	} else {
		r, status, hint = nfs.runTxn(func(txn Txn) Result {
			return nfs.filesys.WRITE(txn, inum, off, bs)
		})
	}

	if status == nfstypes.NFS3ERR_JUKEBOX {
		go nfs.ZeroFreeSpace(inum, hint)
	}
	reply.Status = status
	if status != nfstypes.NFS3_OK {
		util.DPrintf(1, "NFS Write error %d", status)
		return reply
	}

	attrs := r.(nfs_spec.Fattr3)
	reply.Resok.Count = nfstypes.Count3(cnt)
	if unstable {
		reply.Resok.Committed = nfstypes.UNSTABLE
	} else {
		reply.Resok.Committed = nfstypes.FILE_SYNC
	}
	reply.Resok.File_wcc.After.Attributes_follow = true
	decodeFattr3(attrs, inum, &reply.Resok.File_wcc.After.Attributes)
	return reply
}

func (nfs *Nfs) NFSPROC3_CREATE(args nfstypes.CREATE3args) (reply nfstypes.CREATE3res) {
	util.DPrintf(1, "NFS Create %v\n", args)
	defer nfs.reportOp(nfstypes.NFSPROC3_CREATE, time.Now())

	inum := fh2ino(args.Where.Dir)
	nameseq := filenameToBytes(args.Where.Name)
	if !args.How.Obj_attributes.Uid.Set_it {
		args.How.Obj_attributes.Uid.Set_it = true
		args.How.Obj_attributes.Uid.Uid = nfstypes.Uid3(nfs.uid)
	}
	if !args.How.Obj_attributes.Gid.Set_it {
		args.How.Obj_attributes.Gid.Set_it = true
		args.How.Obj_attributes.Gid.Gid = nfstypes.Gid3(nfs.gid)
	}
	how := encodeCreateHow(args.How)

	r, status, hint := nfs.runTxn(func(txn Txn) Result {
		return nfs.filesys.CREATE(txn, inum, nameseq, how)
	})
	if status == nfstypes.NFS3ERR_JUKEBOX {
		go nfs.ZeroFreeSpace(inum, hint)
	}
	reply.Status = status
	if status != nfstypes.NFS3_OK {
		util.DPrintf(1, "NFS Create error %v", status)
		return reply
	}
	create := r.(nfs_spec.CreateResult)

	finum := create.Dtor_ino()

	reply.Resok.Obj.Handle_follows = true
	reply.Resok.Obj.Handle = Fh{Ino: finum}.MakeFh3()
	reply.Resok.Obj_attributes.Attributes_follow = true
	decodeFattr3(create.Dtor_attrs(), finum, &reply.Resok.Obj_attributes.Attributes)
	reply.Resok.Dir_wcc.Before.Attributes_follow = true
	decodeBefore(create.Dtor_dir__before(), &reply.Resok.Dir_wcc.Before.Attributes)
	reply.Resok.Dir_wcc.After.Attributes_follow = true
	decodeFattr3(create.Dtor_dir__attrs(), inum, &reply.Resok.Dir_wcc.After.Attributes)
	return reply
}

func (nfs *Nfs) NFSPROC3_MKDIR(args nfstypes.MKDIR3args) (reply nfstypes.MKDIR3res) {
	util.DPrintf(1, "NFS Mkdir %v\n", args)
	defer nfs.reportOp(nfstypes.NFSPROC3_MKDIR, time.Now())

	inum := fh2ino(args.Where.Dir)
	name := filenameToBytes(args.Where.Name)
	if !args.Attributes.Uid.Set_it {
		args.Attributes.Uid.Set_it = true
		args.Attributes.Uid.Uid = nfstypes.Uid3(nfs.uid)
	}
	if !args.Attributes.Gid.Set_it {
		args.Attributes.Gid.Set_it = true
		args.Attributes.Gid.Gid = nfstypes.Gid3(nfs.gid)
	}
	sattr := encodeSattr3(args.Attributes)

	r, status, _ := nfs.runTxn(func(txn Txn) Result {
		return nfs.filesys.MKDIR(txn, inum, name, sattr)
	})
	reply.Status = status
	if status != nfstypes.NFS3_OK {
		util.DPrintf(1, "NFS Mkdir error %v", status)
		return reply
	}
	ino_r := r.(nfs_spec.CreateResult)
	finum := ino_r.Dtor_ino()

	reply.Resok.Obj.Handle_follows = true
	reply.Resok.Obj.Handle = Fh{Ino: finum}.MakeFh3()
	reply.Resok.Obj_attributes.Attributes_follow = true
	decodeFattr3(ino_r.Dtor_attrs(), finum, &reply.Resok.Obj_attributes.Attributes)
	reply.Resok.Dir_wcc.Before.Attributes_follow = true
	decodeBefore(ino_r.Dtor_dir__before(), &reply.Resok.Dir_wcc.Before.Attributes)
	reply.Resok.Dir_wcc.After.Attributes_follow = true
	decodeFattr3(ino_r.Dtor_dir__attrs(), inum, &reply.Resok.Dir_wcc.After.Attributes)
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

func (nfs *Nfs) NFSPROC3_REMOVE(args nfstypes.REMOVE3args) (reply nfstypes.REMOVE3res) {
	util.DPrintf(1, "NFS Remove %v\n", args)
	defer nfs.reportOp(nfstypes.NFSPROC3_REMOVE, time.Now())

	inum := fh2ino(args.Object.Dir)
	name := filenameToBytes(args.Object.Name)

	hint_r, status, _ := nfs.runTxn(func(txn Txn) Result {
		return nfs.filesys.REMOVE(txn, inum, name)
	})
	reply.Status = status
	if status != nfstypes.NFS3_OK {
		util.DPrintf(1, "NFS Remove error %v", status)
		return reply
	}
	r := hint_r.(nfs_spec.RemoveResult)
	go nfs.ZeroFreeSpace(r.Dtor_ino(), r.Dtor_sz())

	reply.Resok.Dir_wcc.After.Attributes_follow = true
	decodeFattr3(r.Dtor_d__attrs(), inum, &reply.Resok.Dir_wcc.After.Attributes)
	reply.Resok.Dir_wcc.Before.Attributes_follow = true
	decodeBefore(r.Dtor_dir__before(), &reply.Resok.Dir_wcc.Before.Attributes)

	return reply
}

func (nfs *Nfs) NFSPROC3_RMDIR(args nfstypes.RMDIR3args) nfstypes.RMDIR3res {
	util.DPrintf(1, "NFS Rmdir %v\n", args)
	var reply nfstypes.RMDIR3res
	defer nfs.reportOp(nfstypes.NFSPROC3_RMDIR, time.Now())

	inum := fh2ino(args.Object.Dir)
	name := filenameToBytes(args.Object.Name)

	_, status, _ := nfs.runTxn(func(txn Txn) Result {
		return nfs.filesys.RMDIR(txn, inum, name)
	})
	reply.Status = status
	if status != nfstypes.NFS3_OK {
		util.DPrintf(1, "NFS Rmdir error %v", status)
	}

	return reply
}

func (nfs *Nfs) runWithLocks(f func(txn Txn, locks dafny.Sequence) Result) (v interface{}, status nfstypes.Nfsstat3) {
	locks := lock_order.Companion_Default___.EmptyLockHint()
	for {
		txn := nfs.filesys.Begin()
		r := f(txn, locks)
		r = dirfs.Companion_Default___.HandleResult(r, txn, true)
		v, status, _ = parseResult(r)
		if r.Is_Err() && r.Dtor_err().Is_LockOrderViolated() {
			util.DPrintf(3, "Rename violated lock order, restarting")
			locks = r.Dtor_err().Dtor_locks()
			continue
		}
		return
	}
}

func (nfs *Nfs) NFSPROC3_RENAME(args nfstypes.RENAME3args) (reply nfstypes.RENAME3res) {
	util.DPrintf(1, "NFS Rename %v\n", args)
	defer nfs.reportOp(nfstypes.NFSPROC3_RENAME, time.Now())

	src_inum := fh2ino(args.From.Dir)
	src_name := filenameToBytes(args.From.Name)
	dst_inum := fh2ino(args.To.Dir)
	dst_name := filenameToBytes(args.To.Name)

	_, status := nfs.runWithLocks(func(txn Txn, locks dafny.Sequence) Result {
		return nfs.filesys.RENAME(txn, locks, src_inum, src_name, dst_inum, dst_name)
	})

	reply.Status = status
	if status != nfstypes.NFS3_OK {
		util.DPrintf(1, "NFS Rename error %v", status)
	}

	return reply
}

func (nfs *Nfs) NFSPROC3_LINK(args nfstypes.LINK3args) nfstypes.LINK3res {
	util.DPrintf(1, "NFS Link %v\n", args)
	var reply nfstypes.LINK3res
	reply.Status = nfstypes.NFS3ERR_NOTSUPP
	return reply
}

func (nfs *Nfs) NFSPROC3_READDIR(args nfstypes.READDIR3args) (reply nfstypes.READDIR3res) {
	util.DPrintf(1, "NFS Readdir %v\n", args)
	defer nfs.reportOp(nfstypes.NFSPROC3_READDIR, time.Now())

	inum := fh2ino(args.Dir)
	// NOTE: we ignore args.Count, which gives the maximum allowed size of the
	// returned struct (in bytes, including XDR overhead...)

	r, status, _ := nfs.runTxn(func(txn Txn) Result {
		return nfs.filesys.READDIR(txn, inum)
	})
	reply.Status = status
	if status != nfstypes.NFS3_OK {
		util.DPrintf(1, "NFS Readdir error %v", status)
		return reply
	}
	seq := r.(dafny.Sequence)

	seqlen := seq.Cardinality()
	// TODO: produce this . from Dafny, or add it to every directory
	ents := &nfstypes.Entry3{
		Fileid:    nfstypes.Fileid3(inum),
		Name:      nfstypes.Filename3("."),
		Cookie:    1,
		Nextentry: nil,
	}
	for i := uint32(0); i < seqlen; i++ {
		dirent := seq.Select(i).(memdirents.MemDirEnt)
		dirent2 := dirent.Get_().(memdirents.MemDirEnt_MemDirEnt)

		de_ino := dirent2.Ino
		var de_name []byte = dirent2.Name.Data

		ents = &nfstypes.Entry3{
			Fileid:    nfstypes.Fileid3(de_ino),
			Name:      nfstypes.Filename3(de_name),
			Cookie:    nfstypes.Cookie3(i + 2),
			Nextentry: ents,
		}
	}

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

	stats := nfs.filesys.FSSTAT()
	decodeFsstat3(stats, &reply)

	reply.Status = nfstypes.NFS3_OK
	reply.Resok.Obj_attributes.Attributes_follow = false
	reply.Resok.Invarsec = 0
	return reply
}

func (nfs *Nfs) NFSPROC3_FSINFO(args nfstypes.FSINFO3args) nfstypes.FSINFO3res {
	util.DPrintf(1, "NFS Fsinfo %v\n", args)
	var reply nfstypes.FSINFO3res
	reply.Status = nfstypes.NFS3_OK
	reply.Resok.Rtmax = nfstypes.Uint32(
		typed_fs.Companion_Default___.RD__MAX(),
	)
	reply.Resok.Rtpref = reply.Resok.Rtmax
	reply.Resok.Rtmult = 4096
	reply.Resok.Wtmax = nfstypes.Uint32(
		typed_fs.Companion_Default___.WT__MAX(),
	)
	reply.Resok.Wtpref = reply.Resok.Wtmax
	reply.Resok.Wtmult = 4096
	reply.Resok.Maxfilesize = nfstypes.Size3(
		inode.Companion_Default___.MAX__SZ__u64(),
	)
	// {0, 1} indicates nanosecond-precision timestamps
	reply.Resok.Time_delta = nfstypes.Nfstime3{
		Seconds:  0,
		Nseconds: 1,
	}
	// bitmask of supported features - does not include FSF3_LINK (hard link
	// support) or FSF3_SYMLINK (symbolic links). FSF3_HOMOGENEOUS indicates
	// that the PATHCONF information is static.
	reply.Resok.Properties = nfstypes.Uint32(
		nfstypes.FSF3_HOMOGENEOUS | nfstypes.FSF3_CANSETTIME,
	)
	reply.Resok.Dtpref = 65536
	return reply
}

func (nfs *Nfs) NFSPROC3_PATHCONF(args nfstypes.PATHCONF3args) nfstypes.PATHCONF3res {
	util.DPrintf(1, "NFS Pathconf %v\n", args)
	var reply nfstypes.PATHCONF3res
	reply.Resok.Name_max = nfstypes.Uint32(direntries.Companion_Default___.MAX__FILENAME__SZ())
	// If TRUE, the server will reject any request that includes a name longer
	// than name_max with the error, NFS3ERR_NAMETOOLONG.
	reply.Resok.No_trunc = true
	reply.Resok.Linkmax = 1
	reply.Resok.Case_preserving = true
	reply.Status = nfstypes.NFS3_OK
	return reply
}

func (nfs *Nfs) NFSPROC3_COMMIT(args nfstypes.COMMIT3args) nfstypes.COMMIT3res {
	util.DPrintf(1, "NFS Commit %v\n", args)
	var reply nfstypes.COMMIT3res

	if nfs.asyncWrites {
		nfs.filesys.Fs().Fs().Fs().Fs().Jrnl().Flush()
	}

	reply.Status = nfstypes.NFS3_OK
	return reply
}
