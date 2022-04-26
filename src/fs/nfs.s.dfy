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
  {
    function delete(name: seq<byte>): File
      requires DirFile?
    {
      DirFile(map_delete(dir, name), attrs)
    }
  }

  type Fs = map<FsKinds.Ino, File>

  predicate valid_name(name: seq<byte>)
  {
    && DirEntries.is_pathc(name)
    // the following three paths are specifically disallowed
    && name != [] // ""
    && name != ['.' as byte] // "."
    && name != ['.' as byte, '.' as byte] // ".."
  }

  predicate is_file_fs(ino: FsKinds.Ino, data: Fs)
  {
    ino in data && data[ino].ByteFile?
  }

  predicate is_dir_fs(ino: FsKinds.Ino, data: Fs)
  {
    ino in data && data[ino].DirFile?
  }

  datatype RenameArgs = RenameArgs(
    src: FsKinds.Ino, src_name: seq<byte>,
    dst: FsKinds.Ino, dst_name: seq<byte>)
  {
    predicate Valid()
    {
      DirEntries.is_pathc(src_name) && DirEntries.is_pathc(dst_name)
    }

    predicate same_dir()
    {
      src == dst
    }

    predicate trivial()
    {
      same_dir() && src_name == dst_name
    }
  }

  predicate rename_overwrite_ok(args: RenameArgs, data: Fs)
  {
    && args.Valid()
    && is_dir_fs(args.src, data)
    && is_dir_fs(args.dst, data)
    && args.src_name in data[args.src].dir
  }

  function rename_overwrite_spec(args: RenameArgs, data: Fs): Fs
    requires rename_overwrite_ok(args, data)
  {
    var srcd := data[args.src];
    var srcf := srcd.dir[args.src_name];
    var srcd' := srcd.delete(args.src_name);
    var data1: Fs := data[args.src := srcd'];
    var dstd := data1[args.dst];
    var dstd' := DirFile(dstd.dir[args.dst_name := srcf], dstd.attrs);
    data1[args.dst := dstd']
  }

  // simpler re-statement of rename_overwrite_spec_ok when src and destination coincide,
  // mainly to demonstrate that rename_overwrite_spec is sensible
  function rename_overwrite_spec_same_dir(args: RenameArgs, data: Fs): Fs
    requires args.src == args.dst
    requires rename_overwrite_ok(args, data)
  {
    var d0 := data[args.src];
    var srcf := d0.dir[args.src_name];
    var d := map_delete(d0.dir, args.src_name);
    var d := d[args.dst_name := srcf];
    data[args.src := DirFile(d, d0.attrs)]
  }

  lemma rename_overwrite_spec_same_dir_ok(args: RenameArgs, data: Fs)
    requires rename_overwrite_ok(args, data)
    requires args.src == args.dst
    ensures rename_overwrite_spec_same_dir(args, data) == rename_overwrite_spec(args, data)
  {
  }

  // after the core rename operation, will overwriting the destination file be
  // valid?
  //
  // note that data is before the entire operation; after the initial rename
  // the destination is lost so there isn't enough information to decide this
  predicate rename_cleanup_ok(args: RenameArgs, data: Fs)
    requires is_dir_fs(args.src, data) && is_dir_fs(args.dst, data)
    requires args.src_name in data[args.src].dir
  {
    // we evaluate some of the following after removing the src, which might
    // make a no-op rename valid or make it valid to rename a directory on top
    // of its parent
    var data1: Fs := data[args.src := data[args.src].delete(args.src_name)];
    // there are three ways for the overwrite to be valid:
    var dst1 := data1[args.dst];
    // (1) the destination didn't exist so no overwriting took place
    || (args.dst_name !in dst1.dir)
    || var src := data[args.src];
      var dst := data[args.dst];
      && var src_ino := src.dir[args.src_name];
        var dst_ino := dst.dir[args.dst_name];
        // (2) source and destination are both files
        || (&& is_file_fs(src_ino, data)
          && is_file_fs(dst_ino, data))
        // (3) source and destinations are both directories, and the
        // destination is empty
        || (&& is_dir_fs(src_ino, data)
          && is_dir_fs(dst_ino, data)
          && data1[dst_ino].dir == map[])
  }

  // rename with cleanup of any overwritten files
  //
  // note this is the entire rename spec, since the original data is needed to
  // express the right cleanup
  function rename_spec(args: RenameArgs, data: Fs): Fs
    requires is_dir_fs(args.src, data) && is_dir_fs(args.dst, data)
    requires rename_overwrite_ok(args, data)
  {
    // get the old destination file
    var dst := data[args.dst];
    var data: Fs := rename_overwrite_spec(args, data);
    // no cleanup needed if destination didn't exist or src and dst refer to
    // the same file
    if args.dst_name !in dst.dir || args.trivial()
    then data
    else
      var dst_ino := dst.dir[args.dst_name];
      map_delete(data, dst_ino)
  }

  predicate rename_ok(args: RenameArgs, data: Fs)
  {
    && rename_overwrite_ok(args, data)
    && rename_cleanup_ok(args, data)
  }


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

  predicate has_before_attrs(attrs: Inode.Attrs, before: BeforeAttr)
  {
    && attrs.mtime == before.mtime
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
  datatype BeforeAttr = BeforeAttr(size: uint64, mtime: Inode.NfsTime)

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
  datatype CreateResult = CreateResult(ino: FsKinds.Ino, attrs: Fattr3, dir_before: BeforeAttr, dir_attrs: Fattr3)
  // ino and sz are just a hint
  datatype RemoveResult = RemoveResult(ino: FsKinds.Ino, sz: uint64, dir_before: BeforeAttr, d_attrs: Fattr3)

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
