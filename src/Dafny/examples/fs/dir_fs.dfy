include "byte_fs.dfy"
include "mem_dirent.dfy"

module DirFs
{
  import opened Std
  import opened Machine
  import opened ByteSlice
  import opened Fs
  import opened FsKinds
  import opened JrnlTypes
  import opened JrnlSpec
  import opened Alloc

  import opened DirEntries
  import opened MemDirEntries
  import opened ByteFs

  import C = Collections

  datatype File =
    | ByteFile(data: seq<byte>)
    | DirFile(dir: Directory)
  {
    static const empty := ByteFile([])
    static const emptyDir := DirFile(map[])
  }

  type FsData = map<Ino, seq<byte>>
  type Data = map<Ino, File>

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
      }
    }
  }

  datatype Result<T> =
    | Ok(v: T)
    | Err(err: Error)
  {
    const IsError?: bool := !this.Ok?

    const ErrBadHandle?: bool := Err? && err.BadHandle?
    const ErrInval?: bool := Err? && err.Inval?
    const ErrNoent?: bool := Err? && err.Noent?
    const ErrIsDir?: bool := Err? && err.IsDir?
    const ErrNotDir?: bool := Err? && err.NotDir?

    function method Coerce<U>(): Result<U>
      requires IsError?
    {
      Err(this.err)
    }

    function method Val(): T
      requires this.Ok?
    {
      this.v
    }

    function method err_code(): uint32
    {
      match this {
        case Ok(_) => 0
        case Err(err) => err.nfs3_code()
      }
    }
  }

  method HandleResult<T>(r: Result<T>, txn: Txn) returns (r':Result<T>)
    requires txn.Valid()
    ensures r.IsError? ==> r'.IsError?
  {
    if r.IsError? {
      txn.Abort();
      return r;
    }
    var ok := txn.Commit();
    if !ok {
      return Err(ServerFault);
    }
    return r;
  }

  datatype Attributes = Attributes(is_dir: bool, size: uint64)

  class DirFilesys
  {
    // external abstract state
    //
    // domain consists of allocated inodes
    ghost var data: map<Ino, File>

    // internal state, tracking exactly how directories are encoded
    // domain is just the inodes that are allocated directories
    ghost var dirents: map<Ino, Dirents>
    const fs: ByteFilesys<()>
    const ialloc: MaxAllocator

    static const rootIno: Ino := 1 as Ino;

    ghost const Repr: set<object> := {this} + fs.Repr + ialloc.Repr

    static const iallocMax: uint64 := super.num_inodes as uint64 - 8

    predicate is_invalid(ino: Ino) reads this
    { ino !in data && ino !in dirents }

    predicate is_file(ino: Ino) reads this
    { ino in data && ino !in dirents && data[ino].ByteFile? }

    predicate is_dir(ino: Ino) reads this
    { ino in data && ino in dirents && data[ino].DirFile? }

    predicate {:opaque} is_of_type(ino: Ino, t: Inode.InodeType)
      reads this
    {
      && (t.InvalidType? ==> is_invalid(ino))
      && (t.FileType? ==> is_file(ino))
      && (t.DirType? ==> is_dir(ino))
    }

    lemma mk_dir_type(ino: Ino)
      requires fs.fs.Valid()
      requires is_dir(ino)
      requires fs.inode_types()[ino] == Inode.DirType
      ensures is_of_type(ino, fs.inode_types()[ino])
    {
      reveal is_of_type();
    }

    lemma mk_file_type(ino: Ino)
      requires fs.fs.Valid()
      requires is_file(ino)
      requires fs.inode_types()[ino] == Inode.FileType
      ensures is_of_type(ino, fs.inode_types()[ino])
    {
      reveal is_of_type();
    }

    lemma mk_invalid_type(ino: Ino)
      requires fs.fs.Valid()
      requires is_invalid(ino)
      requires fs.inode_types()[ino] == Inode.InvalidType
      ensures is_of_type(ino, fs.inode_types()[ino])
    {
      reveal is_of_type();
    }

    predicate ValidTypes()
      reads this, fs.fs
      requires Fs.ino_dom(fs.fs.metadata)
    {
      forall ino: Ino :: is_of_type(ino, fs.inode_types()[ino])
    }

    lemma invert_dir(ino: Ino)
      requires Fs.ino_dom(fs.fs.metadata)
      requires ValidTypes()
      requires is_dir(ino)
      ensures fs.inode_types()[ino] == Inode.DirType
    {
      reveal is_of_type();
      ghost var t := fs.inode_types()[ino];
      assert is_of_type(ino, t);
      if t == Inode.InvalidType {}
      else if t == Inode.FileType {}
    }

    predicate ValidAlloc()
      reads ialloc.Repr, fs.Repr
    {
      && ialloc.Valid()
      && ialloc.max == iallocMax
      && ialloc.Repr !! fs.Repr
    }

    twostate lemma ValidAlloc_monotonic()
      requires old(ValidAlloc())
      ensures ValidAlloc()
    {}

    predicate {:opaque} ValidRoot()
      reads this
    {
      && is_dir(rootIno)
      && rootIno != 0
    }

    predicate Valid_dirent_at(ino: Ino, fsdata: FsData)
      reads this
      requires ino_dom(fsdata)
    {
      ino in dirents ==> fsdata[ino] == dirents[ino].enc()
    }

    predicate Valid_file_at(ino: Ino, fsdata: FsData)
      reads this
      requires ino_dom(fsdata)
    {
      is_file(ino) ==> this.data[ino] == ByteFile(fsdata[ino])
    }

    predicate Valid_dir_at(ino: Ino)
      reads this
    {
      is_dir(ino) ==> this.data[ino] == DirFile(dirents[ino].dir)
    }

    predicate Valid_invalid_at(ino: Ino, fsdata: FsData)
      requires ino_dom(fsdata)
      reads this
    {
      is_invalid(ino) ==> fsdata[ino] == []
    }

    predicate {:opaque} Valid_data_at(ino: Ino, fsdata: FsData)
      requires ino_dom(fsdata)
      reads this
    {
        && Valid_dirent_at(ino, fsdata)
        && Valid_file_at(ino, fsdata)
        && Valid_dir_at(ino)
        && Valid_invalid_at(ino, fsdata)
    }

    predicate ValidData()
      requires fs.fs.Valid()
      reads this, fs.Repr
    {
      forall ino: Ino :: Valid_data_at(ino, fs.data())
    }

    lemma get_data_at(ino: Ino)
      requires fs.fs.Valid() && ValidData()
      ensures Valid_dirent_at(ino, fs.data())
      ensures Valid_file_at(ino, fs.data())
      ensures Valid_dir_at(ino)
      ensures Valid_invalid_at(ino, fs.data())
    {
      reveal Valid_data_at();
      assert Valid_data_at(ino, fs.data());
    }

    lemma mk_data_at(ino: Ino)
      requires fs.fs.Valid()
      requires Valid_dirent_at(ino, fs.data())
      requires Valid_file_at(ino, fs.data())
      requires Valid_dir_at(ino)
      requires Valid_invalid_at(ino, fs.data())
      ensures Valid_data_at(ino, fs.data())
    {
      reveal Valid_data_at();
    }

    twostate lemma ValidData_change_one(ino: Ino)
      requires old(fs.fs.Valid()) && old(ValidData()) && old(ValidTypes())
      requires fs.fs.Valid()
      requires Valid_data_at(ino, fs.data())
      requires is_of_type(ino, fs.inode_types()[ino])
      requires (forall ino': Ino | ino' != ino ::
      && fs.data()[ino'] == old(fs.data()[ino'])
      && (ino' in dirents ==> ino' in old(dirents) && dirents[ino'] == old(dirents[ino']))
      && (ino' in data ==> ino' in old(data) && data[ino'] == old(data[ino']))
      && (ino' !in data ==> ino' !in old(data))
      && (ino' !in dirents ==> ino' !in old(dirents))
      && fs.inode_types()[ino'] == old(fs.inode_types()[ino']))
      ensures ValidData()
      ensures ValidTypes()
    {
      var ino0 := ino;
      assert ValidTypes() by {
        reveal is_of_type();
      }
      var fsdata0 := old(fs.data());
      var fsdata := fs.data();
      forall ino: Ino | ino != ino0
        ensures Valid_data_at(ino, fsdata)
      {
        reveal Valid_data_at();
        assert old(Valid_data_at(ino, fsdata0));
        assert ino in dirents ==> ino in old(dirents);
        assert is_file(ino) ==> old(is_file(ino));
      }
    }

    predicate ValidDirFs()
      requires fs.fs.Valid()
      reads Repr
    {
      && ValidTypes()
      && ValidAlloc()
      && ValidRoot()
      && ValidData()
    }

    predicate Valid()
      reads Repr
    {
      && fs.Valid()
      && ValidDirFs()
    }

    predicate ValidIno(ino: Ino, i: Inode.Inode)
      reads Repr
    {
      && fs.fs.ValidIno(ino, i)
      && ValidDirFs()
    }

    constructor Init(fs: ByteFilesys<()>)
      requires fs.Valid()
      requires fs.data() == map ino: Ino {:trigger} :: if ino == rootIno then Dirents.zero.enc() else []
      requires fs.inode_types() == map ino: Ino {:trigger} :: if ino == rootIno then Inode.DirType else Inode.InvalidType
      ensures Valid()
      ensures this.rootIno == rootIno
      ensures data == map[rootIno := File.emptyDir]
    {
      this.fs := fs;
      var dirents0 : map<Ino, Dirents> := map[rootIno := Dirents.zero];
      this.dirents := dirents0;
      this.data := map[rootIno := File.emptyDir];
      var ialloc := new MaxAllocator(iallocMax);
      ialloc.MarkUsed(rootIno);
      this.ialloc := ialloc;
      new;
      Dirents.zero_dir();
      assert ValidData() by {
        reveal Valid_data_at();
      }
      assert ValidRoot() by { reveal ValidRoot(); }
      assert ValidTypes() by { reveal is_of_type(); }
    }

    static method createRootDir(fs: ByteFilesys<()>, txn: Txn, ino: Ino) returns (ok: bool)
      modifies fs.Repr
      requires fs.Valid() ensures ok ==> fs.Valid()
      requires fs.fs.has_jrnl(txn)
      requires fs.data()[ino] == []
      ensures ok ==>
      && fs.data() == old(fs.data()[ino := Dirents.zero.enc()])
      && fs.inode_types() == old(fs.inode_types()[ino := Inode.DirType])
    {
      var i := fs.startInode(txn, ino);
      i := fs.setType(ino, i, Inode.DirType);

      var emptyDir := Dirents.zero.encode();
      Dirents.zero.enc_len();
      ok, i := fs.appendIno(txn, ino, i, emptyDir);
      if !ok {
        return;
      }
      assert fs.data()[ino] == Dirents.zero.enc();
      fs.finishInode(txn, ino, i);
      assert fs.Valid();
    }

    static method New(d: Disk) returns (fs: Option<DirFilesys>)
      ensures fs.Some? ==> fresh(fs.x) && fs.x.Valid()
      ensures fs.Some? ==> fs.x.data == map[fs.x.rootIno := DirFile(map[])]
    {
      var fs_ := new ByteFilesys.Init(d);

      var txn := fs_.jrnl.Begin();
      var ok := createRootDir(fs_, txn, rootIno);
      if !ok {
        return None;
      }
      ok := txn.Commit();
      if !ok {
        return None;
      }
      assert fs_.Valid();

      var dir_fs := new DirFilesys.Init(fs_);
      return Some(dir_fs);
    }

    method Begin() returns (txn: Txn)
      requires Valid()
      ensures fs.fs.has_jrnl(txn)
    {
      txn := fs.fs.fs.jrnl.Begin();
    }

    method startInode(txn: Txn, ino: Ino)
      returns (i: Inode.Inode)
      modifies fs.fs.fs
      requires fs.fs.has_jrnl(txn)
      requires Valid()
      ensures ValidIno(ino, i) && i.meta.ty == fs.inode_types()[ino]
      ensures fs.fs.fs.cur_inode == Some( (ino, i) )
      ensures data == old(data)
      ensures dirents == old(dirents)
    {
      i := fs.startInode(txn, ino);
      fs.inode_metadata(ino, i);
      assert ValidData();
    }

    method readDirentsInode(txn: Txn, d_ino: Ino, i: Inode.Inode)
      returns (dents: MemDirents)
      requires ValidIno(d_ino, i)
      requires fs.fs.has_jrnl(txn)
      requires is_dir(d_ino)
      ensures dents.val == dirents[d_ino]
      ensures fresh(dents.Repr)
    {
      assert Valid_dirent_at(d_ino, fs.data()) by {
        get_data_at(d_ino);
      }
      assert |fs.data()[d_ino]| == 4096 by {
        dirents[d_ino].enc_len();
      }
      var bs := fs.readInternal(txn, d_ino, i, 0, 4096);
      dents := new MemDirents(bs, dirents[d_ino]);
    }

    method readDirents(txn: Txn, d_ino: Ino)
      returns (r: Result<MemDirents>)
      modifies fs.fs.fs
      requires Valid() ensures Valid()
      ensures unchanged(this)
      requires fs.fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> is_invalid(d_ino)
      ensures r.ErrNotDir? ==> is_file(d_ino)
      ensures r.Err? ==> r.err.BadHandle? || r.err.NotDir?
      ensures r.Ok? ==>
      && is_dir(d_ino)
      && r.v.val == dirents[d_ino]
      && fresh(r.v.Repr)
    {
      var i := startInode(txn, d_ino);
      if !i.meta.ty.DirType? {
        fs.finishInodeReadonly(d_ino, i);
        assert ValidData();
        if i.meta.ty.InvalidType? {
          assert is_invalid(d_ino) by { reveal is_of_type(); }
          return Err(BadHandle);
        }
        // is a file
        assert is_file(d_ino) by { reveal is_of_type(); }
        return Err(NotDir);
      }
      assert is_dir(d_ino) by { reveal is_of_type(); }
      var dents := readDirentsInode(txn, d_ino, i);
      fs.finishInodeReadonly(d_ino, i);
      assert ValidData();
      return Ok(dents);
    }

    static method writeDirentsToFs(fs: ByteFilesys<()>, txn: Txn, d_ino: Ino, dents: MemDirents)
      returns (ok:bool)
      modifies fs.Repr
      requires fs.Valid() ensures fs.Valid()
      requires dents.Valid()
      requires fs.fs.has_jrnl(txn)
      requires |fs.data()[d_ino]| == 4096
      ensures fs.types_unchanged()
      ensures ok ==> fs.data() == old(fs.data()[d_ino := dents.val.enc()])
      ensures !ok ==> fs.data() == old(fs.data())
      ensures dents.val == old(dents.val)
    {
      assert dents.Repr !! fs.Repr;
      var i := fs.startInode(txn, d_ino);
      var bs := dents.encode();
      dents.val.enc_len();
      C.splice_all(fs.data()[d_ino], bs.data);
      ok, i := fs.alignedWrite(txn, d_ino, i, bs, 0);
      fs.finishInode(txn, d_ino, i);
      if !ok {
        return;
      }
      assert fs.data()[d_ino] == dents.val.enc();
    }

    method {:timeLimitMultiplier 2} writeDirents(txn: Txn, d_ino: Ino, dents: MemDirents)
      returns (ok:bool)
      modifies Repr
      requires fs.fs.has_jrnl(txn)
      requires Valid() ensures ok ==> Valid()
      requires dents.Valid()
      requires is_dir(d_ino)
      ensures ok ==>
           && dirents == old(dirents[d_ino := dents.val])
           && data == old(data[d_ino := DirFile(dents.dir())])
    {
      assert |fs.data()[d_ino]| == 4096 by {
        get_data_at(d_ino);
        dirents[d_ino].enc_len();
      }
      assert fs.inode_types()[d_ino] == Inode.DirType by {
        invert_dir(d_ino);
      }
      ghost var dents_val := dents.val;
      ok := writeDirentsToFs(fs, txn, d_ino, dents);
      if !ok {
        return;
      }

      dirents := dirents[d_ino := dents_val];
      data := data[d_ino := DirFile(dents_val.dir)];

      assert is_dir(d_ino);
      assert is_of_type(d_ino, fs.inode_types()[d_ino]) by { reveal is_of_type(); }
      mk_data_at(d_ino);
      ValidData_change_one(d_ino);
      assert ValidRoot() by { reveal ValidRoot(); }
    }

    // allocInode finds an invalid inode and prepares it for writes
    method allocInode(txn: Txn) returns (ok: bool, ino: Ino, i: Inode.Inode)
      modifies fs.fs.fs, ialloc.Repr
      requires Valid()
      ensures ok ==> ValidIno(ino, i)
      ensures !ok ==> Valid()
      requires fs.fs.has_jrnl(txn)
      ensures dirents == old(dirents)
      ensures data == old(data)
      ensures fs.types_unchanged()
      ensures ok ==> old(is_invalid(ino)) && is_invalid(ino) && ino != rootIno
      ensures ok ==> fs.data()[ino] == []
      ensures ok ==> ino != 0
    {
      ino := ialloc.Alloc();
      i := fs.startInode(txn, ino);
      fs.inode_metadata(ino, i);
      assert is_of_type(ino, i.meta.ty);
      assert ValidIno(ino, i) by {
      }
      ok := i.meta.ty.InvalidType?;
      if !ok {
        fs.finishInodeReadonly(ino, i);
        return;
      }
      assert is_invalid(ino) && ino != rootIno by {
        reveal is_of_type();
        reveal ValidRoot();
      }
      assert fs.data()[ino] == [] by {
        get_data_at(ino);
      }
    }

    // private
    //
    // creates a file disconnected from the file system (which is perfectly
    // legal but useless for most clients)
    method allocFile(txn: Txn)
      returns (ok: bool, ino: Ino)
      modifies Repr
      requires Valid() ensures ok ==> Valid()
      requires fs.fs.has_jrnl(txn)
      ensures dirents == old(dirents)
      ensures ok ==>
      && old(is_invalid(ino))
      && ino != 0
      && data == old(data[ino := File.empty])
      ensures !ok ==> data == old(data)
    {
      var i;
      ok, ino, i := this.allocInode(txn);
      if !ok {
        return;
      }

      assert this !in fs.Repr;
      i := fs.setType(ino, i, Inode.FileType);
      fs.finishInode(txn, ino, i);
      data := data[ino := File.empty];

      // NOTE(tej): this assertion takes far longer than I expected
      assert is_file(ino);
      mk_file_type(ino);
      mk_data_at(ino);
      ValidData_change_one(ino);

      assert ValidRoot() by { reveal ValidRoot(); }
    }

    method writeEmptyDir(txn: Txn, ino: Ino, i: Inode.Inode)
      returns (ok: bool)
      modifies fs.Repr
      requires ValidIno(ino, i) ensures ok ==> fs.Valid()
      requires fs.fs.has_jrnl(txn)
      requires fs.data()[ino] == []
      ensures ok ==> fs.data() == old(fs.data()[ino := Dirents.zero.enc()])
      ensures ok ==> fs.inode_types() == old(fs.inode_types()[ino := Inode.DirType])
      ensures unchanged(this)
    {
      var i := i;
      i := fs.setType(ino, i, Inode.DirType);
      var emptyDir := Dirents.zero.encode();
      Dirents.zero.enc_len();
      ok, i := fs.appendIno(txn, ino, i, emptyDir);
      if !ok {
        return;
      }
      assert fs.data()[ino] == Dirents.zero.enc();

      fs.finishInode(txn, ino, i);
    }

    // private
    //
    // creates a directory disconnected from the file system (which is perfectly
    // legal but useless for most clients)
    method allocDir(txn: Txn) returns (ok: bool, ino: Ino)
      modifies Repr
      requires Valid() ensures ok ==> Valid()
      requires fs.fs.has_jrnl(txn)
      ensures ok ==>
      && old(is_invalid(ino))
      && ino != 0
      && data == old(data[ino := File.emptyDir])
      && dirents == old(dirents[ino := Dirents.zero])
      && is_dir(ino)
    {
      var i;
      ok, ino, i := this.allocInode(txn);
      if !ok {
        return;
      }

      assert this !in fs.Repr;
      ok := writeEmptyDir(txn, ino, i);
      if !ok {
        return;
      }

      dirents := dirents[ino := Dirents.zero];
      data := data[ino := File.emptyDir];
      assert File.emptyDir.DirFile?;
      assert is_dir(ino);

      Dirents.zero_dir();
      assert is_dir(ino);
      mk_dir_type(ino);
      mk_data_at(ino);
      ValidData_change_one(ino);

      assert ValidRoot() by { reveal ValidRoot(); }
    }

    // linkInode inserts a new entry e' into d_ino
    //
    // requires that e'.name is not already in the directory (in that case we
    // need to insert in a slightly different way that isn't implemented)
    method linkInode(txn: Txn, d_ino: Ino, dents: MemDirents, e': MemDirEnt)
      returns (ok: bool)
      modifies Repr, dents.Repr, e'.name
      requires Valid()
      ensures ok ==> Valid()
      requires fs.fs.has_jrnl(txn)
      requires dents.Valid() && e'.Valid()
      requires is_dir(d_ino) && dirents[d_ino] == dents.val
      requires e'.used() && dents.val.findName(e'.path()) >= 128
      ensures ok ==>
      && data == old(
      var d0 := data[d_ino].dir;
      var d' := DirFile(d0[e'.path() := e'.ino]);
      data[d_ino := d'])
    {
      assert data[d_ino] == DirFile(dents.val.dir) by {
        get_data_at(d_ino);
      }
      var i := dents.findFree();
      if !(i < 128) {
        // no space in directory
        ok := false;
        return;
      }
      ghost var path := e'.path();
      ghost var ino := e'.ino;
      ghost var d := dents.val.dir;
      dents.insert_ent(i, e');
      ghost var d' := dents.val.dir;
      assert d' == d[path := ino];
      ok := writeDirents(txn, d_ino, dents);
      if !ok {
        return;
      }
      assert data[d_ino] == DirFile(d');
    }

    method CREATE(txn: Txn, d_ino: Ino, name: Bytes)
      returns (r: Result<Ino>)
      modifies Repr
      requires Valid() ensures r.Ok? ==> Valid()
      requires is_pathc(name.data)
      requires fs.fs.has_jrnl(txn)
      ensures r.Ok? ==>
      (var ino := r.v;
      && old(is_dir(d_ino))
      && old(is_invalid(ino))
      && data == old(
        var d := data[d_ino].dir;
        var d' := DirFile(d[name.data := ino]);
        data[ino := File.empty][d_ino := d'])
      )
    {
      var dents_r := readDirents(txn, d_ino);
      if dents_r.IsError? {
        return dents_r.Coerce();
      }
      var dents := dents_r.v;
      var ok, ino := allocFile(txn);
      if !ok {
        return Err(NoSpc);
      }
      assert ino_ok: ino !in old(data);
      var name_opt := dents.findName(name);
      if name_opt.None? {
        // TODO: support creating a file and overwriting existing (rather than
        // failing here)
        return Err(ServerFault);
      }
      ok := linkInode(txn, d_ino, dents, MemDirEnt(name, ino));
      if !ok {
        return Err(NoSpc);
      }
      // assert data == old(data[ino := File.empty][d_ino := DirFile(d')]);
      reveal ino_ok;
      return Ok(ino);
    }

    method GETATTR(txn: Txn, ino: Ino)
      returns (r: Result<Attributes>)
      modifies fs.fs.fs
      requires Valid() ensures Valid()
      requires fs.fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> ino !in data
      ensures r.Ok? ==>
          (var attrs := r.v;
          && ino in data
          && attrs.is_dir == data[ino].DirFile?
          && data[ino].ByteFile? ==> attrs.size as nat == |data[ino].data|
          //&& data[ino].DirFile? ==> attrs.size as nat == |data[ino].dir|
          )
    {
      var i := startInode(txn, ino);
      if i.meta.ty.InvalidType? {
        assert is_invalid(ino) by { reveal is_of_type(); }
        fs.finishInodeReadonly(ino, i);
        assert ValidData() by {
          // reveal ValidFiles();
        }
        return Err(BadHandle);
      }
      if i.meta.ty.DirType? {
        assert is_dir(ino) by { reveal is_of_type(); }
        var dents := readDirentsInode(txn, ino, i);
        fs.finishInodeReadonly(ino, i);
        assert Valid() by {
          // assert ValidFiles() by { reveal ValidFiles(); }
        }
        // NOTE: not sure what the size of a directory is supposed to be, so
        // just return its encoded size in bytes
        var attrs := Attributes(true, 4096);
        return Ok(attrs);
      }
      // is a file
      assert i.meta.ty.FileType?;
      assert is_file(ino) by { reveal is_of_type(); }
      fs.finishInodeReadonly(ino, i);
      assert Valid() by {
        // assert ValidFiles() by { reveal ValidFiles(); }
      }
      var attrs := Attributes(false, i.sz);
      return Ok(attrs);
    }

    method openFile(txn: Txn, ino: Ino)
      returns (r:Result<Inode.Inode>)
      modifies fs.fs.fs
      requires Valid()
      requires fs.fs.has_jrnl(txn)
      ensures r.Ok? ==>
      && ValidIno(ino, r.v)
      && fs.fs.fs.cur_inode == Some ( (ino, r.v) )
      && is_file(ino)
      && old(is_file(ino))
      ensures !r.Ok? ==> Valid()
      ensures fs.data() == old(fs.data())
      ensures r.ErrBadHandle? ==> is_invalid(ino)
      ensures r.ErrIsDir? ==> is_dir(ino)
      ensures r.Err? ==> r.err.BadHandle? || r.err.IsDir?
      ensures unchanged(this)
    {
      var i := startInode(txn, ino);
      if i.meta.ty.InvalidType? {
        assert is_invalid(ino) by { reveal is_of_type(); }
        fs.finishInodeReadonly(ino, i);
        // assert ValidFiles() by { reveal ValidFiles(); }
        return Err(BadHandle);
      }
      if i.meta.ty.DirType? {
        assert is_dir(ino) by { reveal is_of_type(); }
        fs.finishInodeReadonly(ino, i);
        // assert ValidFiles() by { reveal ValidFiles(); }
        return Err(IsDir);
      }
      assert old(is_file(ino)) && is_file(ino) by { reveal is_of_type(); }
      return Ok(i);
    }

    // TODO: add support for writes to arbitrary offsets
    method {:timeLimitMultiplier 2} Append(txn: Txn, ino: Ino, bs: Bytes)
      returns (r: Result<()>)
      modifies Repr, bs
      requires Valid()
      // nothing to say in error case (need to abort)
      ensures r.Ok? ==> Valid()
      requires fs.fs.has_jrnl(txn)
      requires bs.Valid() && 0 < bs.Len() <= 4096
      ensures r.ErrBadHandle? ==> ino !in old(data)
      ensures (r.Err? && r.err.Inval?) ==> ino in old(data) && old(data[ino].DirFile?)
      ensures r.Ok? ==>
      && ino in old(data) && old(data[ino].ByteFile?)
      && data == old(
      var d := data[ino].data;
      var d' := d + bs.data;
      data[ino := ByteFile(d')])
    {
      var i_r := openFile(txn, ino);
      if i_r.IsError? {
        if i_r.err.IsDir? {
          return Err(Inval);
        }
        return i_r.Coerce();
      }
      assert dirents == old(dirents);
      assert fs.inode_types()[ino] == Inode.FileType by {
        reveal is_of_type();
      }
      var i := i_r.v;
      assert ValidIno(ino, i);
      ghost var d0: seq<byte> := old(fs.data()[ino]);
      assert d0 == old(data[ino].data) by {
        get_data_at(ino);
      }
      if i.sz + bs.Len() > Inode.MAX_SZ_u64 {
        // fs.finishInodeReadonly(ino, i);
        return Err(FBig);
      }
      fs.inode_metadata(ino, i);
      assert this !in fs.Repr;
      var ok;
      ok, i := fs.appendIno(txn, ino, i, bs);
      if !ok {
        // fs.finishInode(txn, ino, i);
        return Err(NoSpc);
      }

      fs.finishInode(txn, ino, i);

      ghost var f' := ByteFile(d0 + old(bs.data));
      data := data[ino := f'];

      assert Valid() by {
        assert dirents == old(dirents);
        assert is_of_type(ino, fs.inode_types()[ino]) by {
          assert is_file(ino);
          reveal is_of_type();
        }
        mk_data_at(ino);
        ValidData_change_one(ino);
        assert ValidRoot() by { reveal ValidRoot(); }
      }
      return Ok(());
    }

    method READ(txn: Txn, ino: Ino, off: uint64, len: uint64)
      returns (r: Result<Bytes>)
      modifies fs.fs.fs
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> ino !in data
      ensures r.ErrInval? ==> ino in data && data[ino].DirFile?
      ensures unchanged(this)
      ensures r.Ok? ==>
      (var bs := r.v;
      && ino in data && data[ino].ByteFile?
      && off as nat + len as nat <= |data[ino].data|
      && bs.data == data[ino].data[off as nat..off as nat + len as nat]
      )
    {
      if len > 4096 {
        // we should really return a short read
        var bs := NewBytes(0);
        return Err(ServerFault);
      }
      var i_r := openFile(txn, ino);
      if i_r.IsError? {
        if i_r.err.IsDir? {
          return Err(Inval);
        }
        return i_r.Coerce();
      }
      var i := i_r.v;
      var bs, ok := fs.read_txn_with_inode(txn, ino, i, off, len);
      if !ok {
        // TODO: I believe this should never happen, short reads are supposed to
        // return partial data and an EOF flag
        return Err(ServerFault);
      }
      get_data_at(ino);
      assert Valid() by {
        assert ValidData() by {
          reveal Valid_data_at();
        }
      }
      return Ok(bs);
    }

    method MKDIR(txn: Txn, d_ino: Ino, name: Bytes)
      returns (r: Result<Ino>)
      modifies Repr
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.fs.has_jrnl(txn)
      requires is_pathc(name.data)
      ensures (r.Err? && r.err.Exist?) ==> old(is_dir(d_ino)) && name.data in old(data[d_ino].dir)
      ensures r.Ok? ==>
      (var ino := r.v;
      && old(is_dir(d_ino))
      && old(is_invalid(ino))
      && data == old(
        var d := data[d_ino].dir;
        var d' := DirFile(d[name.data := ino]);
        data[ino := File.emptyDir][d_ino := d'])
      )
    {
      var dents_r := readDirents(txn, d_ino);
      if dents_r.IsError? {
        return dents_r.Coerce();
      }
      var dents := dents_r.v;
      assert is_dir(d_ino);
      var ok, ino := allocDir(txn);
      if !ok {
        return Err(NoSpc);
      }
      get_data_at(d_ino);
      assert ino != d_ino;
      assert ino_ok: ino !in old(data);
      var name_opt := dents.findName(name);
      if name_opt.Some? {
        dents.val.findName_found(name.data);
        return Err(Exist);
      }
      ok := linkInode(txn, d_ino, dents, MemDirEnt(name, ino));
      if !ok {
        return Err(NoSpc);
      }
      reveal ino_ok;
      return Ok(ino);
    }

    method LOOKUP(txn: Txn, d_ino: Ino, name: Bytes)
      returns (r:Result<Ino>)
      modifies fs.fs.fs
      requires Valid() ensures Valid()
      requires fs.fs.has_jrnl(txn)
      requires is_pathc(name.data)
      ensures r.ErrBadHandle? ==> d_ino !in data
      ensures r.ErrNoent? ==> is_dir(d_ino) && name.data !in data[d_ino].dir
      ensures r.Ok? ==>
      (var ino := r.v;
      && is_dir(d_ino)
      && name.data in data[d_ino].dir && data[d_ino].dir[name.data] == ino && ino != 0
      )
    {
      var dents_r := readDirents(txn, d_ino);
      if dents_r.IsError? {
        return dents_r.Coerce();
      }
      var dents := dents_r.v;
      assert DirFile(dents.dir()) == data[d_ino] by {
        get_data_at(d_ino);
      }
      var name_opt := dents.findName(name);
      if name_opt.None? {
        dents.val.findName_not_found(name.data);
        return Err(Noent);
      }
      var ino: Ino := name_opt.x.1;
      dents.val.findName_found(name.data);
      return Ok(ino);
    }

    method zeroInode(txn: Txn, ino: Ino, i: Inode.Inode)
      modifies fs.Repr
      requires ValidIno(ino, i) ensures fs.Valid()
      requires fs.fs.has_jrnl(txn)
      ensures fs.data() == old(fs.data()[ino := []])
      ensures fs.inode_types() == old(fs.inode_types()[ino := Inode.InvalidType])
      ensures unchanged(this)
    {
      var i := i;
      i := fs.setType(ino, i, Inode.InvalidType);
      i := fs.shrinkToEmpty(txn, ino, i);
      fs.finishInode(txn, ino, i);
    }

    // this is a low-level function that deletes an inode (currently restricted
    // to files) from the tree; Unlink currently doesn't call this so we leave a
    // dangling inode
    method {:timeLimitMultiplier 2} removeInode(txn: Txn, ino: Ino)
      returns (r: Result<()>)
      modifies Repr
      requires Valid() ensures Valid()
      requires fs.fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> ino !in data && data == old(data)
      ensures r.ErrIsDir? ==> ino in data && data[ino].DirFile? && data == old(data)
      ensures r.Err? ==> r.err.BadHandle? || r.err.IsDir?
      ensures r.Ok? ==>
      && old(ino in data)
      && data == old(map_delete(data, ino))
    {
      var i := startInode(txn, ino);
      if i.meta.ty == Inode.InvalidType {
        assert is_invalid(ino) by { reveal is_of_type(); }
        fs.finishInodeReadonly(ino, i);
        return Err(BadHandle);
      }
      if i.meta.ty == Inode.DirType {
        // TODO: removeInode doesn't yet support directories
        assert is_dir(ino) by { reveal is_of_type(); }
        fs.finishInodeReadonly(ino, i);
        return Err(IsDir);
      }
      assert is_file(ino) by { reveal is_of_type(); }
      zeroInode(txn, ino, i);
      ialloc.Free(ino);
      //map_delete_not_in(data, ino);
      data := map_delete(data, ino);

      assert dirents == old(dirents);
      mk_invalid_type(ino);
      mk_data_at(ino);
      ValidData_change_one(ino);
      assert ValidRoot() by { reveal ValidRoot(); }
      return Ok(());
    }

    method REMOVE(txn: Txn, d_ino: Ino, name: Bytes)
      returns (r: Result<()>)
      modifies Repr
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> d_ino !in old(data)
      ensures r.ErrNoent? ==> old(is_dir(d_ino)) && name.data !in old(data[d_ino].dir)
      ensures r.ErrIsDir? ==>
      && (old(is_dir(d_ino))
      && name.data in old(data[d_ino].dir))
      && (var ino := old(data[d_ino].dir[name.data]);
        && ino in old(data)
        && old(data[ino].DirFile?))
      ensures r.Ok? ==>
      && old(is_dir(d_ino))
      && name.data in old(data[d_ino].dir)
      && data ==
        (var d0 := old(data[d_ino].dir);
        var d' := map_delete(d0, name.data);
        map_delete(old(data)[d_ino := DirFile(d')], d0[name.data]))
    {
      var dents_r := readDirents(txn, d_ino);
      if dents_r.IsError? {
        return dents_r.Coerce();
      }
      assert was_dir: old(is_dir(d_ino));
      var dents := dents_r.v;
      assert DirFile(dents.dir()) == data[d_ino] by {
        get_data_at(d_ino);
      }
      ghost var d0: Directory := old(data[d_ino].dir);
      var name_opt := dents.findName(name);
      if name_opt.None? {
        dents.val.findName_not_found(name.data);
        assert name.data !in data[d_ino].dir;
        return Err(Noent);
      }
      var i := name_opt.x.0;
      var ino := name_opt.x.1;
      dents.val.findName_found(name.data);
      assert name_present: name.data in old(data[d_ino].dir);
      dents.deleteAt(i);
      ghost var d': Directory := dents.dir();
      assert d' == map_delete(d0, name.data);
      var ok := writeDirents(txn, d_ino, dents);
      if !ok {
        return Err(NoSpc);
      }
      ghost var data1 := data;
      assert data1 == old(data)[d_ino := DirFile(d')];
      var remove_r := removeInode(txn, ino);
      if remove_r.IsError? {
        if remove_r.ErrBadHandle? {
          assert map_delete(data, d0[name.data]) == data1;
          reveal was_dir;
          reveal name_present;
          //assert Valid();
          return Ok(());
        }
        return remove_r.Coerce();
      }
      reveal was_dir;
      reveal name_present;
      //assert Valid();
      assert data == map_delete(data1, d0[name.data]);
      return Ok(());
    }

    // TODO: implement RMDIR, a variation of REMOVE that needs to also check the
    // inode being removed and confirm that it's empty

    method READDIR(txn: Txn, d_ino: Ino)
      returns (r: Result<seq<MemDirEnt>>)
      modifies fs.fs.fs
      requires Valid() ensures Valid()
      requires fs.fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> d_ino !in data
      ensures r.Ok? ==>
      (var dents_seq := r.v;
      && d_ino in data
      && data[d_ino].DirFile?
      && seq_to_dir(mem_seq_val(dents_seq)) == data[d_ino].dir
      && |dents_seq| == |data[d_ino].dir|
      )
    {
      var dents_r := readDirents(txn, d_ino);
      if dents_r.IsError? {
        return dents_r.Coerce();
      }
      var dents := dents_r.v;
      assert DirFile(dents.dir()) == data[d_ino] by {
        get_data_at(d_ino);
      }
      var dents_seq := dents.usedDents();
      return Ok(dents_seq);
    }

    // TODO:
    //
    // 1. Append (done)
    // 2. Read (done)
    // 3. CreateDir (done)
    // 4. Write
    // 5. Rename (maybe?)
    // 6. Unlink (done)

  }
}
