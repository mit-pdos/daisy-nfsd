include "byte_fs.dfy"
include "dirent.dfy"

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
  import opened ByteFs

  import C = Collections

  datatype File =
    | ByteFile(data: seq<byte>)
    | DirFile(dir: Directory)
  {
    static const empty := ByteFile([])
    static const emptyDir := DirFile(map[])
  }

  datatype Error =
    | Noent
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

    predicate ValidTypes()
      reads this, fs.fs
      requires Fs.ino_dom(fs.fs.metadata)
    {
      forall ino: Ino :: is_of_type(ino, fs.inode_types()[ino])
    }

    lemma type_invert(ino: Ino)
      requires fs.fs.Valid()
      requires ValidTypes()
      ensures ino !in data ==> fs.inode_types()[ino].InvalidType? && ino !in dirents
      ensures ino in data && data[ino].ByteFile? ==> fs.inode_types()[ino].FileType? && ino !in dirents
      ensures ino in dirents ==> fs.inode_types()[ino].DirType? && ino in data
    {
      var t := fs.inode_types()[ino];
      assert is_of_type(ino, t);
      reveal is_of_type();
      if t.InvalidType? { return; }
      if t.FileType? { return; }
      if t.DirType? { return; }
      assert false;
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
      reads this, fs.fs
      requires Fs.ino_dom(fs.fs.metadata)
    {
      // the root inode is actually a directory
      && fs.inode_types()[rootIno].DirType?
      && rootIno != 0
    }

    predicate ValidDirents()
      requires fs.fs.Valid()
      reads this, fs.Repr
    {
      forall ino:Ino | ino in dirents ::
        fs.data()[ino] == dirents[ino].enc()
    }

    predicate {:opaque} ValidFiles()
      requires fs.fs.Valid()
      reads this, fs.Repr
    {
      forall ino:Ino | is_file(ino) ::
        data[ino] == ByteFile(fs.data()[ino])
    }

    predicate {:opaque} ValidDirs()
      reads this
    {

      forall ino:Ino | is_dir(ino) ::
        data[ino] == DirFile(dirents[ino].dir)
    }

    predicate ValidData()
      requires fs.fs.Valid()
      reads this, fs.Repr
    {
      && ValidFiles()
      && ValidDirs()
    }

    predicate ValidUnusedInodes()
      requires fs.fs.Valid()
      reads this, fs.Repr
    {
      forall ino:Ino | is_invalid(ino) :: fs.data()[ino] == []
    }

    predicate ValidDirFs()
      requires fs.fs.Valid()
      reads Repr
    {
      && ValidTypes()
      && ValidAlloc()
      && ValidRoot()
      && ValidDirents()
      && ValidData()
      && ValidUnusedInodes()
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

    twostate lemma valid_change_file(ino: Ino, f: File)
      requires old(fs.fs.Valid()) && old(ValidDirFs())
      requires fs.fs.Valid()
      requires f.ByteFile?
      requires fs.inode_types() == old(fs.inode_types())
      //requires fs.data() == old(fs.data()[ino := f.data])
      requires dirents == old(dirents)
      requires others_unchanged: (
      var ino0 := ino;
      forall ino:Ino | ino != ino0 :: fs.data()[ino] == old(fs.data()[ino])
      )
      requires fs.data()[ino] == f.data
      requires data == old(data[ino := f])
      requires old(is_file(ino))
      ensures ValidTypes() && ValidAlloc() && ValidRoot() && ValidDirents() && ValidDirs()
    {
      assert fs.data() == old(fs.data()[ino := f.data]) by {
        reveal others_unchanged;
      }
      ghost var t0 := old(fs.inode_types()[ino]);
      assert t0 == Inode.FileType by {
        reveal is_of_type();
        if t0 == Inode.InvalidType {
          assert t0.InvalidType?;
        } else if t0 == Inode.FileType {
          assert t0.FileType?;
        } else {}
      }
      assert old(is_file(ino)) && is_file(ino) by {
        assert old(fs.inode_types()[ino]) == Inode.FileType;
        reveal is_of_type();
      }
      assert fs.inode_types()[ino] == Inode.FileType;
      assert is_of_type(ino, fs.inode_types()[ino]) by { reveal is_of_type(); }
      ghost var ino0 := ino;

      forall ino: Ino
        ensures is_of_type(ino, fs.inode_types()[ino])
      {
        if ino == ino0 {  }
        else {
          assert (ino in data) == old(ino in data);
          assert (ino in dirents) == old(ino in dirents);
          reveal is_of_type();
          match fs.inode_types()[ino] {
            case InvalidType => {
              assert old(fs.inode_types()[ino]).InvalidType?;
            }
            case FileType => {
              assert old(fs.inode_types()[ino]).FileType?;
            }
            case DirType => {
              assert old(fs.inode_types()[ino]).DirType?;
            }
          }
        }
      }
      assert ValidTypes();
      assert ValidRoot() by { reveal ValidRoot(); }
      assert ValidDirs() by { reveal ValidDirs(); }
      assert ValidDirents();
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
        reveal ValidFiles();
        reveal ValidDirs();
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
      assert ValidData() by {
        reveal ValidFiles();
      }
    }

    method readDirentsInode(txn: Txn, d_ino: Ino, i: Inode.Inode)
      returns (dents: Dirents)
      requires ValidIno(d_ino, i)
      requires fs.fs.has_jrnl(txn)
      requires is_dir(d_ino)
      ensures dents == dirents[d_ino]
    {
      assert |fs.data()[d_ino]| == 4096 by {
        dirents[d_ino].enc_len();
      }
      var bs := fs.readInternal(txn, d_ino, i, 0, 4096);
      dents := Dirents.decode(bs, dirents[d_ino]);
    }

    method readDirents(txn: Txn, d_ino: Ino)
      returns (r: Result<Dirents>)
      modifies fs.fs.fs
      requires Valid() ensures Valid()
      ensures unchanged(this)
      requires fs.fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> is_invalid(d_ino)
      ensures r.ErrNotDir? ==> is_file(d_ino)
      ensures r.Err? ==> r.err.BadHandle? || r.err.NotDir?
      ensures r.Ok? ==> is_dir(d_ino) && r.v == dirents[d_ino]
    {
      var i := startInode(txn, d_ino);
      if !i.meta.ty.DirType? {
        fs.finishInodeReadonly(d_ino, i);
        assert ValidData() by {
          reveal ValidFiles();
        }
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
      assert ValidData() by {
        reveal ValidFiles();
      }
      return Ok(dents);
    }

    static method writeDirentsToFs(fs: ByteFilesys<()>, txn: Txn, d_ino: Ino, dents: Dirents)
      returns (ok:bool)
      modifies fs.Repr
      requires fs.Valid() ensures fs.Valid()
      requires fs.fs.has_jrnl(txn)
      requires |fs.data()[d_ino]| == 4096
      ensures fs.types_unchanged()
      ensures ok ==> fs.data() == old(fs.data()[d_ino := dents.enc()])
      ensures !ok ==> fs.data() == old(fs.data())
    {
      var i := fs.startInode(txn, d_ino);
      var bs := dents.encode();
      assert |bs.data| == 4096 by {
        dents.enc_len();
      }
      ok, i := fs.alignedWrite(txn, d_ino, i, bs, 0);
      fs.finishInode(txn, d_ino, i);
      if !ok {
        return;
      }
      assert fs.data()[d_ino] == dents.enc();
    }

    method {:verify false} writeDirents(txn: Txn, d_ino: Ino, dents: Dirents)
      returns (ok:bool)
      modifies Repr
      requires fs.fs.has_jrnl(txn)
      requires Valid() ensures ok ==> Valid()
      requires is_dir(d_ino)
      ensures ok ==>
           && dirents == old(dirents[d_ino := dents])
           && data == old(data[d_ino := DirFile(dents.dir)])
    {
      assert |fs.data()[d_ino]| == 4096 by {
        dirents[d_ino].enc_len();
      }
      ok := writeDirentsToFs(fs, txn, d_ino, dents);
      if !ok {
        return;
      }

      dirents := dirents[d_ino := dents];
      data := data[d_ino := DirFile(dents.dir)];

      // assert is_dir(d_ino);
      assert ValidFiles() by { reveal ValidFiles(); }
      assert ValidDirs() by { reveal ValidDirs(); }
      assert ValidRoot() by { reveal ValidRoot(); }
      assert ValidTypes() by { reveal is_of_type(); }
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
      ensures ok ==> ino != 0
    {
      ino := ialloc.Alloc();
      i := fs.startInode(txn, ino);
      fs.inode_metadata(ino, i);
      assert is_of_type(ino, i.meta.ty);
      assert ValidIno(ino, i) by {
        assert ValidFiles() by { reveal ValidFiles(); }
      }
      ok := i.meta.ty.InvalidType?;
      if !ok {
        fs.finishInodeReadonly(ino, i);
        assert Valid() by {
          assert ValidFiles() by { reveal ValidFiles(); }
        }
      }
      assert ok ==> is_invalid(ino) && ino != rootIno by {
        reveal is_of_type();
        reveal ValidRoot();
      }
    }

    // private
    //
    // creates a file disconnected from the file system (which is perfectly
    // legal but useless for most clients)
    //
    // TODO: this is extremely slow to verify despite doing very little,
    // something might be wrong
    method {:timeLimitMultiplier 2} {:verify false} allocFile(txn: Txn)
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
      i := fs.setType(ino, i, Inode.FileType);
      fs.finishInode(txn, ino, i);
      data := data[ino := File.empty];
      assert is_of_type(ino, Inode.FileType) by {
        reveal is_of_type();
      }
      assert ValidDirs() by {
        reveal ValidDirs();
      }
      assert ValidFiles() by {
        reveal ValidFiles();
      }
      assert ValidTypes() by { reveal is_of_type(); }
      assert ValidRoot() by { reveal ValidRoot(); }
    }

    method {:verify false} writeEmptyDir(txn: Txn, ino: Ino, i: Inode.Inode)
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
    //
    // TODO: this is extremely slow to verify
    method {:timeLimitMultiplier 2} {:verify false} allocDir(txn: Txn) returns (ok: bool, ino: Ino)
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

      ok := writeEmptyDir(txn, ino, i);
      if !ok {
        return;
      }

      dirents := dirents[ino := Dirents.zero];
      data := data[ino := File.emptyDir];
      assert File.emptyDir.DirFile?;
      assert is_dir(ino);

      Dirents.zero_dir();
      //assert fs.data()[ino] == dirents[ino].enc();
      assert ValidDirents();
      assert ValidDirs() by {
        reveal ValidDirs();
      }
      assert ValidFiles() by {
        reveal ValidFiles();
      }
      assert ValidTypes() by { reveal is_of_type(); }
      assert ValidRoot() by { reveal ValidRoot(); }
    }

    // linkInode inserts a new entry e' into d_ino
    //
    // requires that e'.name is not already in the directory (in that case we
    // need to insert in a slightly different way that isn't implemented)
    method linkInode(txn: Txn, d_ino: Ino, dents: Dirents, e': DirEnt)
      returns (ok: bool)
      modifies Repr
      requires Valid()
      ensures ok ==> Valid()
      requires fs.fs.has_jrnl(txn)
      requires is_dir(d_ino) && dirents[d_ino] == dents
      requires e'.used() && dents.findName(e'.name) >= 128
      ensures ok ==>
      && data == old(
      var d0 := data[d_ino].dir;
      var d' := DirFile(d0[e'.name := e'.ino]);
      data[d_ino := d'])
    {
      assert data[d_ino] == DirFile(dents.dir) by {
        reveal ValidDirs();
      }
      var i := dents.findFree();
      if !(i < 128) {
        // no space in directory
        ok := false;
        return;
      }
      dents.insert_ent_dir(e');
      ghost var d := dents.dir;
      var dents := dents.insert_ent(i, e');
      ghost var d' := dents.dir;
      assert d' == d[e'.name := e'.ino];
      ok := writeDirents(txn, d_ino, dents);
      if !ok {
        return;
      }
      assert data[d_ino] == DirFile(d');
    }

    method CREATE(txn: Txn, d_ino: Ino, name: PathComp)
      returns (r: Result<Ino>)
      modifies Repr
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.fs.has_jrnl(txn)
      ensures r.Ok? ==>
      (var ino := r.v;
      && old(is_dir(d_ino))
      && old(is_invalid(ino))
      && data == old(
        var d := data[d_ino].dir;
        var d' := DirFile(d[name := ino]);
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
      if dents.findName(name) < 128 {
        // TODO: support creating a file and overwriting existing (rather than
        // failing here)
        return Err(ServerFault);
      }
      ok := linkInode(txn, d_ino, dents, DirEnt(name, ino));
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
          && data[ino].DirFile? ==> attrs.size as nat == |data[ino].dir|
          )
    {
      var i := startInode(txn, ino);
      if i.meta.ty.InvalidType? {
        assert is_invalid(ino) by { reveal is_of_type(); }
        fs.finishInodeReadonly(ino, i);
        assert ValidData() by {
          reveal ValidFiles();
        }
        return Err(BadHandle);
      }
      if i.meta.ty.DirType? {
        assert is_dir(ino) by { reveal is_of_type(); }
        var dents := readDirentsInode(txn, ino, i);
        fs.finishInodeReadonly(ino, i);
        assert Valid() by {
          assert ValidFiles() by { reveal ValidFiles(); }
        }
        var num_entries := dents.numValid();
        var attrs := Attributes(true, num_entries);
        return Ok(attrs);
      }
      // is a file
      assert i.meta.ty.FileType?;
      assert is_file(ino) by { reveal is_of_type(); }
      fs.finishInodeReadonly(ino, i);
      assert Valid() by {
        assert ValidFiles() by { reveal ValidFiles(); }
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
    {
      var i := startInode(txn, ino);
      if i.meta.ty.InvalidType? {
        assert is_invalid(ino) by { reveal is_of_type(); }
        fs.finishInodeReadonly(ino, i);
        assert ValidFiles() by { reveal ValidFiles(); }
        return Err(BadHandle);
      }
      if i.meta.ty.DirType? {
        assert is_dir(ino) by { reveal is_of_type(); }
        fs.finishInodeReadonly(ino, i);
        assert ValidFiles() by { reveal ValidFiles(); }
        return Err(IsDir);
      }
      assert old(is_file(ino)) && is_file(ino) by { reveal is_of_type(); }
      return Ok(i);
    }

    // TODO: add support for writes to arbitrary offsets
    method {:timeLimitMultiplier 2} {:verify false} Append(txn: Txn, ino: Ino, bs: Bytes)
      returns (r: Result<()>)
      modifies Repr, bs
      requires Valid()
      // nothing to say in error case (need to abort)
      ensures r.Ok? ==> Valid()
      requires fs.fs.has_jrnl(txn)
      requires bs.Valid() && 0 < bs.Len() <= 4096
      ensures r.ErrBadHandle? ==> data == old(data) && ino !in data
      ensures r.ErrIsDir? ==> data == old(data) && ino in data && data[ino].DirFile?
      ensures r.Ok? ==>
      && ino in old(data) && old(data[ino].ByteFile?)
      && data == old(
      var d := data[ino].data;
      var d' := d + bs.data;
      data[ino := ByteFile(d')])
    {
      var i_r := openFile(txn, ino);
      if i_r.IsError? {
        return i_r.Coerce();
      }
      assert old(is_file(ino));
      var i := i_r.v;
      assert ValidIno(ino, i);
      ghost var d0: seq<byte> := old(fs.data()[ino]);
      assert d0 == old(data[ino].data) by {
        reveal ValidFiles();
      }
      if i.sz + bs.Len() > Inode.MAX_SZ_u64 {
        fs.finishInodeReadonly(ino, i);
        return Err(FBig);
      }
      fs.inode_metadata(ino, i);
      var ok;
      ok, i := fs.appendIno(txn, ino, i, bs);
      if !ok {
        fs.finishInode(txn, ino, i);
        return Err(NoSpc);
      }

      fs.finishInode(txn, ino, i);

      ghost var f' := ByteFile(d0 + old(bs.data));
      data := data[ino := f'];
      valid_change_file(ino, f');
      assert ValidFiles() by { reveal ValidFiles(); }
      return Ok(());
    }

    method READ(txn: Txn, ino: Ino, off: uint64, len: uint64)
      returns (r: Result<Bytes>)
      modifies fs.fs.fs
      requires Valid() ensures Valid()
      requires fs.fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> ino !in data
      ensures r.ErrInval? ==> ino in data && data[ino].DirFile?
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
      assume false;
      var i := i_r.v;
      var bs, ok := fs.read_txn_with_inode(txn, ino, i, off, len);
      if !ok {
        assert ValidFiles() by { reveal ValidFiles(); }
        // TODO: I believe this should never happen, short reads are supposed to
        // return partial data and an EOF flag
        return Err(ServerFault);
      }
      assert Valid() by {
        assert ValidFiles() by { reveal ValidFiles(); }
      }
      reveal ValidFiles();
      return Ok(bs);
    }

    method {:verify false} MKDIR(txn: Txn, d_ino: Ino, name: PathComp)
      returns (r: Result<Ino>)
      modifies Repr
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.fs.has_jrnl(txn)
      ensures r.Ok? ==>
      (var ino := r.v;
      && old(is_dir(d_ino))
      && old(is_invalid(ino))
      && data == old(
        var d := data[d_ino].dir;
        var d' := DirFile(d[name := ino]);
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
      assert ino != d_ino;
      assert ino_ok: ino !in old(data);
      if dents.findName(name) < 128 {
        ok := false;
        return;
      }
      ok := linkInode(txn, d_ino, dents, DirEnt(name, ino));
      if !ok {
        return Err(NoSpc);
      }
      reveal ino_ok;
      return Ok(ino);
    }

    method LOOKUP(txn: Txn, d_ino: Ino, name: PathComp)
      returns (r:Result<Ino>)
      modifies fs.fs.fs
      requires Valid() ensures Valid()
      requires fs.fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> d_ino !in data
      ensures r.ErrNoent? ==> is_dir(d_ino) && name !in data[d_ino].dir
      ensures r.Ok? ==>
      (var ino := r.v;
      && is_dir(d_ino)
      && name in data[d_ino].dir && data[d_ino].dir[name] == ino && ino != 0
      )
    {
      var dents_r := readDirents(txn, d_ino);
      if dents_r.IsError? {
        return dents_r.Coerce();
      }
      var dents := dents_r.v;
      assert DirFile(dents.dir) == data[d_ino] by {
        reveal ValidDirs();
      }
      var i := dents.findName(name);
      if !(i < 128) {
        dents.findName_not_found(name);
        return Err(Noent);
      }
      var ino := dents.s[i].ino;
      dents.findName_found(name);
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
      i := fs.shrinkToEmpty(ino, i);
      fs.finishInode(txn, ino, i);
    }

    // this is a low-level function that deletes an inode (currently restricted
    // to files) from the tree; Unlink currently doesn't call this so we leave a
    // dangling inode
    method {:timeLimitMultiplier 2} {:verify false} removeInode(txn: Txn, ino: Ino)
      returns (r: Result<()>)
      modifies Repr
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> ino !in data && data == old(data)
      ensures r.Ok? ==>
      && old(ino in data)
      && data == old(map_delete(data, ino))
    {
      var i := startInode(txn, ino);
      if i.meta.ty == Inode.InvalidType {
        assert is_invalid(ino) by { reveal is_of_type(); }
        //fs.finishInodeReadonly(ino, i);
        //assert ValidFiles() by { reveal ValidFiles(); }
        return Err(BadHandle);
      }
      if i.meta.ty == Inode.DirType {
        // removeInode doesn't yet support directories
        //fs.finishInodeReadonly(ino, i);
        //assert Valid() by {
        //  assert ValidFiles() by { reveal ValidFiles(); }
        //}
        return Err(ServerFault);
      }
      assert is_file(ino) by { reveal is_of_type(); }
      zeroInode(txn, ino, i);
      ialloc.Free(ino);
      //map_delete_not_in(data, ino);
      data := map_delete(data, ino);

      assert fs.inode_types()[ino].InvalidType?;
      assert is_invalid(ino);
      assert ValidTypes() by { reveal is_of_type(); }
      assert ValidDirs() by { reveal ValidDirs(); }
      assert ValidFiles() by { reveal ValidFiles(); }
      assert ValidRoot() by { reveal ValidRoot(); }
      return Ok(());
    }

    method {:verify false} REMOVE(txn: Txn, d_ino: Ino, name: PathComp)
      returns (r: Result<()>)
      modifies Repr
      requires Valid() ensures Valid()
      requires fs.fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> d_ino !in data && data == old(data)
      ensures r.Ok? ==>
      && old(is_dir(d_ino))
      && name in old(data[d_ino].dir)
      && data == old(
        var d0 := data[d_ino].dir;
        var d' := map_delete(d0, name);
        data[d_ino := DirFile(d')]
      )
    {
      var dents_r := readDirents(txn, d_ino);
      if dents_r.IsError? {
        return dents_r.Coerce();
      }
      var dents := dents_r.v;
      assert DirFile(dents.dir) == data[d_ino] by {
        reveal ValidDirs();
      }
      var i := dents.findName(name);
      if !(i < 128) {
        dents.findName_not_found(name);
        assert name !in data[d_ino].dir;
        return Err(Noent);
      }
      dents.findName_found(name);
      dents := dents.deleteAt(i);
      var ok := writeDirents(txn, d_ino, dents);
      if !ok {
        return Err(NoSpc);
      }
      return Ok(());
    }

    // TODO: implement RMDIR, a variation of REMOVE that needs to also check the
    // inode being removed and confirm that it's empty

    method READDIR(txn: Txn, d_ino: Ino)
      returns (r: Result<seq<DirEnt>>)
      modifies fs.fs.fs
      requires Valid() ensures Valid()
      requires fs.fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> d_ino !in data
      ensures r.Ok? ==>
      (var dents_seq := r.v;
      && d_ino in data
      && data[d_ino].DirFile?
      && seq_to_dir(dents_seq) == data[d_ino].dir
      && |dents_seq| == |data[d_ino].dir|
      )
    {
      var dents_r := readDirents(txn, d_ino);
      if dents_r.IsError? {
        return dents_r.Coerce();
      }
      var dents := dents_r.v;
      assert DirFile(dents.dir) == data[d_ino] by {
        reveal ValidDirs();
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
