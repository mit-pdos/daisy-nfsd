include "../machine/bytes.s.dfy"
include "../util/std.dfy"
include "inode/inode.dfy"
// for definition of directories
include "dir/dirent.dfy"

module Nfs {
  import opened Std
  import opened Machine
  import opened ByteSlice
  import Inode
  import DirEntries
  import FsKinds
  import C = Collections

  // DirEntries.Directory = map<PathComp, Ino>
  // where PathComp is a subset type of seq<byte>

  datatype File =
    | ByteFile(data: seq<byte>, attrs: Inode.Attrs)
    | DirFile(dir: DirEntries.Directory, attrs: Inode.Attrs)

   type Data = map<FsKinds.Ino, File>

  datatype Error =
    | Noent
    | Exist
    | NotDir
    | IsDir
    | Inval
    | FBig
    | NoSpc
    | NameTooLong
    | NotEmpty
    | BadHandle
    | ServerFault
    | JukeBox(sz_hint: uint64)
    // this is a purely internal error
    | LockOrderViolated(locks: seq<uint64>)
  {
    function method nfs3_code(): uint32
    {
      match this {
        case Noent => 2
        case Exist => 17
        case NotDir => 20
        case IsDir => 21
        case Inval => 22
        case FBig => 27
        case NoSpc => 28
        case NameTooLong => 63
        case NotEmpty => 66
        case BadHandle => 10001
        case ServerFault => 10006
        case JukeBox(_) => 10008
        case LockOrderViolated(_) => 10008
      }
    }
  }

  const NFS3_OK: uint32 := 0

  datatype Result<T> =
    | Ok(v: T)
    | Err(err: Error)
  {
    const ErrBadHandle?: bool := Err? && err.BadHandle?
    const ErrInval?: bool := Err? && err.Inval?
    const ErrNoent?: bool := Err? && err.Noent?
    const ErrIsDir?: bool := Err? && err.IsDir?
    const ErrNotDir?: bool := Err? && err.NotDir?

    // make this a failure-compatible type

    predicate method IsFailure()
    {
      this.Err?
    }

    function method PropagateFailure<U>(): Result<U>
      requires IsFailure()
    {
      Err(this.err)
    }

    function method Extract(): T
      requires !IsFailure()
    {
      this.v
    }

    // READ and WRITE are not supposed to return Err(IsDir) but should return
    // Err(Inval) when the file is a directory. IsDirToInval transforms just that error
    // condition, from a more primitive method that uses IsDir.
    function method IsDirToInval(): Result<T>
    {
      match this {
        case Ok(v) => Ok(v)
        case Err(err) => if err.IsDir? then Err(Inval) else Err(err)
      }
    }

    function method err_code(): uint32
    {
      match this {
        case Ok(_) => NFS3_OK
        case Err(err) => err.nfs3_code()
      }
    }
  }

  type createverf3 = s:seq<byte> | |s| == 8 ghost witness C.repeat(0 as byte, 8)

  datatype SetTime = DontChange | SetToServerTime | SetToClientTime(time: Inode.NfsTime)

  datatype Sattr3 =
    Sattr3(
    mode: Option<uint32>,
    uid: Option<uint32>,
    gid: Option<uint32>,
    size: Option<uint64>,
    atime: SetTime,
    mtime: SetTime
    )
  {
    static const setNone := Sattr3(None, None, None, None, DontChange, DontChange)
  }

  datatype CreateHow3 =
    | Unchecked(obj_attributes: Sattr3)
    | Guarded(obj_attributes: Sattr3)
    // for simplicity we get the wrapper code to directly give an NFS time
    // (rather than 8 bytes)
    | Exclusive(verf: Inode.NfsTime)
  {
    function method size(): uint64
    {
      if Exclusive? then 0
      else obj_attributes.size.get_default(0)
    }
  }

  predicate has_create_attrs(attrs: Inode.Attrs, how: CreateHow3)
  {
    && attrs.ty.FileType?
    && (!how.Exclusive? ==>
      (var how_attrs := how.obj_attributes;
      && (how_attrs.mode.Some? ==> attrs.mode == how_attrs.mode.x)
      && (how_attrs.uid.Some? ==> attrs.uid == how_attrs.uid.x)
      && (how_attrs.gid.Some? ==> attrs.gid == how_attrs.gid.x)
      && (how_attrs.mtime.SetToClientTime? ==> attrs.mtime == how_attrs.mtime.time)
      ))
  }

  datatype Ftype3 =
    | NFS3REG | NFS3DIR
    | NFS3BLK | NFS3CHR | NFS3LNK | NFS3SOCK | NFS3FIFO
  {
    function method to_uint32(): uint32 {
      match this {
        case NFS3REG => 1
        case NFS3DIR => 2
        case NFS3BLK => 3
        case NFS3CHR => 4
        case NFS3LNK => 5
        case NFS3SOCK => 6
        case NFS3FIFO => 7
      }
    }

    // to catch copy-paste errors
    static lemma to_uint32_inj(t1: Ftype3, t2: Ftype3)
      ensures t1.to_uint32() == t2.to_uint32() ==> t1 == t2
    {}
  }

  datatype Fattr3 = Fattr3(ftype: Ftype3, size: uint64, attrs: Inode.Attrs)

  predicate is_file_attrs(file: File, attr: Fattr3)
  {
    && file.ByteFile? == attr.ftype.NFS3REG?
    && file.DirFile? == attr.ftype.NFS3DIR?
    && file.attrs == attr.attrs
    && (file.ByteFile? ==> |file.data| == attr.size as nat)
    // size of directory is an encoding detail that is leaked to clients
  }

  datatype ReadResult = ReadResult(data: Bytes, eof: bool)
  datatype InoResult = InoResult(ino: FsKinds.Ino, attrs: Fattr3)

  predicate is_read_data(data: seq<byte>, off: nat, len: nat,
    bs: seq<byte>, eof: bool)
  {
    && |bs| <= len
    && (off + |bs| <= |data| ==> bs == data[off..off + |bs|])
    && (eof <==> off + |bs| >= |data|)
  }

  predicate has_root_attrs(attrs: Inode.Attrs, uid: uint32, gid: uint32)
  {
    && attrs.ty.DirType?
    && attrs.uid == uid && attrs.gid == gid
    // Dafny doesn't have octal literals, so write out 0777 carefully
    // the code just uses 511 which is the decimal value of this expression
    && attrs.mode == ((7 as bv32 << 6) | (7 as bv32 << 3) | (7 as bv32)) as uint32
  }

  predicate has_mkdir_attrs(attrs: Inode.Attrs, sattr: Sattr3)
  {
    && attrs.ty.DirType?
    && attrs.mode == sattr.mode.get_default(0)
    && attrs.uid == sattr.uid.get_default(0)
    && attrs.gid == sattr.gid.get_default(0)
    // Linux calls MKDIR with DontChange, but we expect it to get a creation
    // timestamp somehow
    // && (sattr.mtime.DontChange? ==> attrs.mtime == attrs0.mtime)
    && (sattr.mtime.SetToClientTime? ==> attrs.mtime == sattr.mtime.time)
  }

  predicate has_set_attrs(attrs0: Inode.Attrs, attrs: Inode.Attrs, sattr: Sattr3)
  {
    && attrs.ty == attrs0.ty
    && attrs.mode == sattr.mode.get_default(attrs0.mode)
    && attrs.uid == sattr.uid.get_default(attrs0.uid)
    && attrs.gid == sattr.gid.get_default(attrs0.gid)
    && (sattr.mtime.DontChange? ==> attrs.mtime == attrs0.mtime)
    && (sattr.mtime.SetToClientTime? ==> attrs.mtime == sattr.mtime.time)
  }

  predicate has_modify_attrs(attrs0: Inode.Attrs, attrs: Inode.Attrs)
  {
    && attrs.ty == attrs0.ty
    && attrs.mode == attrs0.mode
    && attrs.uid == attrs0.uid
    && attrs.gid == attrs0.gid
    // mtime can change
  }

  datatype Fsstat3 = Fsstat3(
    // bytes in file system / free bytes
    tbytes: uint64, fbytes: uint64,
    // files (inodes) in file system / free files
    tfiles: uint64, ffiles: uint64
    )
  {
    static const zero := Fsstat3(0,0,0,0);
  }

}
