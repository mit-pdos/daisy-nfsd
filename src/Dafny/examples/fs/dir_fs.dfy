include "typed_fs.dfy"
include "mem_dirent.dfy"
include "nfs.s.dfy"

module DirFs
{
  import opened Std
  import opened Machine
  import opened ByteSlice
  import opened Fs
  import opened FsKinds
  import opened JrnlTypes
  import opened JrnlSpec

  import opened DirEntries
  import opened MemDirEnts
  import opened MemDirEntries
  import opened Paths
  import opened TypedFs
  import opened FileCursor
  import opened MemInodes

  import opened Nfs

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

  method HandleResult<T>(r: Result<T>, txn: Txn) returns (r':Result<T>)
    requires txn.Valid()
    ensures r.Err? ==> r'.Err?
  {
    if r.Err? {
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

  datatype ReadResult = ReadResult(data: Bytes, eof: bool)

  class DirFilesys
  {
    // external abstract state
    //
    // domain consists of allocated inodes
    ghost var data: map<Ino, File>

    // internal state, tracking exactly how directories are encoded
    // domain is just the inodes that are allocated directories
    ghost var dirents: map<Ino, Dirents>
    const fs: TypedFilesys

    static const rootIno: Ino := 1 as Ino;

    ghost const Repr: set<object> := {this} + fs.Repr

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
      requires fs.Valid()
      requires is_dir(ino)
      requires fs.types[ino] == Inode.DirType
      ensures is_of_type(ino, fs.types[ino])
    {
      reveal is_of_type();
    }

    lemma mk_file_type(ino: Ino)
      requires fs.Valid()
      requires is_file(ino)
      requires fs.types[ino] == Inode.FileType
      ensures is_of_type(ino, fs.types[ino])
    {
      reveal is_of_type();
    }

    lemma mk_invalid_type(ino: Ino)
      requires fs.Valid()
      requires is_invalid(ino)
      requires fs.types[ino] == Inode.InvalidType
      ensures is_of_type(ino, fs.types[ino])
    {
      reveal is_of_type();
    }

    predicate ValidTypes()
      reads this, fs
      requires fs.ValidDomains()
    {
      forall ino: Ino :: is_of_type(ino, fs.types[ino])
    }

    lemma invert_dir(ino: Ino)
      requires fs.ValidDomains()
      requires ValidTypes()
      requires is_dir(ino)
      ensures fs.types[ino] == Inode.DirType
    {
      reveal is_of_type();
      ghost var t := fs.types[ino];
      assert is_of_type(ino, t);
      if t == Inode.InvalidType {}
      else if t == Inode.FileType {}
      else if t == Inode.DirType {}
    }

    lemma invert_file(ino: Ino)
      requires fs.ValidDomains()
      requires ValidTypes()
      requires is_file(ino)
      ensures fs.types[ino] == Inode.FileType
    {
      reveal is_of_type();
      ghost var t := fs.types[ino];
      assert is_of_type(ino, t);
      if t == Inode.InvalidType {}
      else if t == Inode.FileType {}
      else if t == Inode.DirType {}
    }

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
      ino in dirents ==> |fsdata[ino]| % 4096 == 0 && fsdata[ino] == dirents[ino].enc()
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
      requires fs.ValidDomains()
      reads this, fs
    {
      forall ino: Ino :: Valid_data_at(ino, fs.data)
    }

    lemma get_data_at(ino: Ino)
      requires fs.ValidDomains() && ValidData()
      ensures Valid_dirent_at(ino, fs.data)
      ensures Valid_file_at(ino, fs.data)
      ensures Valid_dir_at(ino)
      ensures Valid_invalid_at(ino, fs.data)
    {
      reveal Valid_data_at();
      assert Valid_data_at(ino, fs.data);
    }

    lemma mk_data_at(ino: Ino)
      requires fs.ValidDomains()
      requires Valid_dirent_at(ino, fs.data)
      requires Valid_file_at(ino, fs.data)
      requires Valid_dir_at(ino)
      requires Valid_invalid_at(ino, fs.data)
      ensures Valid_data_at(ino, fs.data)
    {
      reveal Valid_data_at();
    }

    twostate lemma ValidData_change_one(ino: Ino)
      requires old(fs.ValidDomains()) && old(ValidData()) && old(ValidTypes())
      requires fs.ValidDomains()
      requires Valid_data_at(ino, fs.data)
      requires is_of_type(ino, fs.types[ino])
      requires (forall ino': Ino | ino' != ino ::
      && fs.data[ino'] == old(fs.data[ino'])
      && (ino' in dirents ==> ino' in old(dirents) && dirents[ino'] == old(dirents[ino']))
      && (ino' in data ==> ino' in old(data) && data[ino'] == old(data[ino']))
      && (ino' !in data ==> ino' !in old(data))
      && (ino' !in dirents ==> ino' !in old(dirents))
      && fs.types[ino'] == old(fs.types[ino']))
      ensures ValidData()
      ensures ValidTypes()
    {
      var ino0 := ino;
      assert ValidTypes() by {
        reveal is_of_type();
      }
      var fsdata0 := old(fs.data);
      var fsdata := fs.data;
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
      requires fs.ValidDomains()
      reads this, fs
    {
      && ValidTypes()
      && ValidRoot()
      && ValidData()
    }

    predicate Valid()
      reads Repr
    {
      && fs.Valid()
      && ValidDirFs()
    }

    predicate ValidIno(ino: Ino, i: MemInode)
      reads Repr, i.Repr
    {
      && fs.ValidIno(ino, i)
      && ValidDirFs()
    }

    constructor Init(fs: TypedFilesys)
      requires fs.Valid()
      requires fs.data == map ino: Ino {:trigger} :: if ino == rootIno then Dirents.zero.enc() else []
      requires fs.types == map ino: Ino {:trigger} :: if ino == rootIno then Inode.DirType else Inode.InvalidType
      ensures Valid()
      ensures this.rootIno == rootIno
      ensures data == map[rootIno := File.emptyDir]
    {
      this.fs := fs;
      var dirents0 : map<Ino, Dirents> := map[rootIno := Dirents.zero];
      this.dirents := dirents0;
      this.data := map[rootIno := File.emptyDir];
      new;
      Dirents.zero_dir();
      assert ValidData() by {
        reveal Valid_data_at();
      }
      assert ValidRoot() by { reveal ValidRoot(); }
      assert ValidTypes() by { reveal is_of_type(); }
    }

    static method createRootDir(fs: TypedFilesys, txn: Txn, ino: Ino) returns (ok: bool)
      modifies fs.Repr
      requires fs.Valid() ensures ok ==> fs.Valid()
      requires fs.has_jrnl(txn)
      requires fs.types[ino] == Inode.InvalidType
      requires fs.data[ino] == []
      ensures ok ==>
      && fs.data == old(fs.data[ino := Dirents.zero.enc()])
      && fs.types == old(fs.types[ino := Inode.DirType])
    {
      var i := fs.allocateAt(txn, ino, Inode.DirType);
      ok := writeEmptyDirToFs(fs, txn, ino, i);
    }

    static method New(d: Disk) returns (fs: Option<DirFilesys>)
      ensures fs.Some? ==> fresh(fs.x) && fs.x.Valid()
      ensures fs.Some? ==> fs.x.data == map[fs.x.rootIno := DirFile(map[])]
    {
      var fs_ := new TypedFilesys.Init(d);

      fs_.reveal_valids();
      var txn := fs_.fs.fs.fs.jrnl.Begin();
      var ok := createRootDir(fs_, txn, rootIno);
      if !ok {
        return None;
      }
      fs_.reveal_valids();
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
      ensures fs.has_jrnl(txn)
    {
      fs.reveal_valids();
      txn := fs.fs.fs.fs.jrnl.Begin();
    }

    predicate ValidDirents(dents: MemDirents, d_ino: Ino)
      reads this, dents.Repr(), dents.file.ReprFs
    {
      && dents.Valid()
      && dents.file.fs == this.fs
      && dents.file.ino == d_ino
      && ValidIno(d_ino, dents.file.i)
      && is_dir(d_ino)
      && dirents[d_ino] == dents.val
    }

    method readDirentsInode(txn: Txn, d_ino: Ino, i: MemInode)
      returns (dents: MemDirents)
      requires ValidIno(d_ino, i)
      requires fs.inode_unchanged(d_ino, i.val())
      requires fs.has_jrnl(txn)
      requires is_dir(d_ino)
      ensures fresh(dents.Repr())
      ensures dents.file.i == i
      ensures ValidDirents(dents, d_ino)
      ensures dents.inode_unchanged()
    {
      assert Valid_dirent_at(d_ino, fs.data) by {
        get_data_at(d_ino);
      }
      assert is_dir(d_ino);
      var file := new Cursor(this.fs, d_ino, i);
      dents := new MemDirents(file, dirents[d_ino]);
    }

    twostate predicate dirents_for(new dents: MemDirents, d_ino: Ino)
      reads this, dents.Repr(), dents.file.ReprFs
    {
      && ValidDirents(dents, d_ino)
      && fresh(dents.Repr())
      && fresh(dents.file.i.Repr)
      && dents.inode_unchanged()
    }

    method readDirents(txn: Txn, d_ino: Ino)
      returns (r: Result<MemDirents>)
      modifies fs.fs.fs.fs
      requires Valid()
      ensures r.Err? ==> Valid()
      requires fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> is_invalid(d_ino)
      ensures r.ErrNotDir? ==> is_file(d_ino)
      ensures r.Err? ==> r.err.BadHandle? || r.err.NotDir?
      ensures r.Ok? ==>
      && is_dir(d_ino)
      && dirents_for(r.v, d_ino)
    {
      var ok, i := fs.startInode(txn, d_ino);
      if !ok {
        assert is_invalid(d_ino) by { reveal is_of_type(); }
        return Err(BadHandle);
      }
      if i.ty.FileType? {
        fs.finishInodeReadonly(d_ino, i);
        assert is_file(d_ino) by { reveal is_of_type(); }
        return Err(NotDir);
      }
      assert is_dir(d_ino) by { reveal is_of_type(); }
      var dents := readDirentsInode(txn, d_ino, i);
      //fs.finishInodeReadonly(d_ino, i);
      assert ValidData();
      return Ok(dents);
    }

    /*
    static method writeDirentsToFs(fs: TypedFilesys, txn: Txn, d_ino: Ino, dents: MemDirents)
      returns (ok:bool)
      modifies fs.Repr
      requires fs.Valid() ensures ok ==> fs.Valid()
      requires dents.Valid()
      requires fs.has_jrnl(txn)
      requires |fs.data[d_ino]| == 4096
      ensures fs.types_unchanged()
      ensures ok ==> fs.data == old(fs.data[d_ino := dents.val.enc()])
      ensures dents.val == old(dents.val)
    {
      assert dents.Repr() !! fs.Repr;
      var i;
      ok, i := fs.startInode(txn, d_ino);
      if !ok {
        return;
      }
      var bs := dents.encode();
      C.splice_all(fs.data[d_ino], bs.data);
      ok := fs.writeBlockFile(txn, d_ino, i, bs);
      if !ok {
        return;
      }
      fs.finishInode(txn, d_ino, i);
      assert fs.data[d_ino] == dents.val.enc();
    }

    method writeDirents(txn: Txn, d_ino: Ino, dents: MemDirents)
      returns (ok:bool)
      modifies Repr
      requires fs.has_jrnl(txn)
      requires Valid() ensures ok ==> Valid()
      requires dents.Valid()
      requires is_dir(d_ino)
      ensures ok ==>
           && dirents == old(dirents[d_ino := dents.val])
           && data == old(data[d_ino := DirFile(dents.dir())])
    {
      assert |fs.data[d_ino]| == 4096 by {
        get_data_at(d_ino);
      }
      assert fs.types[d_ino] == Inode.DirType by {
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
      assert is_of_type(d_ino, fs.types[d_ino]) by { reveal is_of_type(); }
      mk_data_at(d_ino);
      ValidData_change_one(d_ino);
      assert ValidRoot() by { reveal ValidRoot(); }
    }
    */

    // private
    //
    // creates a file disconnected from the file system (which is perfectly
    // legal but useless for most clients)
    method allocFile(txn: Txn)
      returns (ok: bool, ino: Ino)
      modifies Repr
      requires Valid() ensures ok ==> Valid()
      requires fs.has_jrnl(txn)
      ensures dirents == old(dirents)
      ensures ok ==>
      && old(is_invalid(ino))
      && ino != 0
      && data == old(data[ino := File.empty])
      ensures !ok ==> data == old(data)
    {
      var i;
      ok, ino, i := fs.allocInode(txn, Inode.FileType);
      if !ok {
        return;
      }
      assert this !in fs.Repr;
      fs.finishInode(txn, ino, i);
      assert old(is_invalid(ino)) by {
        assert old(is_of_type(ino, fs.types[ino]));
        reveal is_of_type();
      }
      data := data[ino := File.empty];

      // NOTE(tej): this assertion takes far longer than I expected
      assert is_file(ino);
      mk_file_type(ino);
      mk_data_at(ino);
      ValidData_change_one(ino);

      assert ValidRoot() by { reveal ValidRoot(); }
    }

    static method writeEmptyDirToFs(fs: TypedFilesys, txn: Txn, ino: Ino, i: MemInode)
      returns (ok: bool)
      modifies fs.Repr, i.Repr
      requires fs.ValidIno(ino, i) ensures ok ==> fs.Valid()
      requires fs.has_jrnl(txn)
      requires fs.data[ino] == []
      ensures fs.types_unchanged()
      ensures ok ==> fs.data == old(fs.data[ino := Dirents.zero.enc()])
    {
      var emptyDir := NewBytes(4096);
      assert emptyDir.data == Dirents.zero.enc() by {
        Dirents.zero_enc();
      }
      ok := fs.write(txn, ino, i, 0, emptyDir);
      if !ok {
        return;
      }
      assert fs.data[ino] == Dirents.zero.enc();

      fs.finishInode(txn, ino, i);
    }

    // private
    //
    // creates a directory disconnected from the file system (which is perfectly
    // legal but useless for most clients)
    method allocDir(txn: Txn) returns (ok: bool, ino: Ino)
      modifies Repr
      requires Valid() ensures ok ==> Valid()
      requires fs.has_jrnl(txn)
      ensures ok ==>
      && old(is_invalid(ino))
      && ino != 0
      && data == old(data[ino := File.emptyDir])
      && dirents == old(dirents[ino := Dirents.zero])
      && is_dir(ino)
    {
      var i;
      ok, ino, i := fs.allocInode(txn, Inode.DirType);
      if !ok {
        return;
      }
      assert old(is_invalid(ino)) by {
        assert old(is_of_type(ino, fs.types[ino]));
        reveal is_of_type();
      }

      assert this !in fs.Repr;
      ok := writeEmptyDirToFs(fs, txn, ino, i);
      if !ok {
        return;
      }

      dirents := dirents[ino := Dirents.zero];
      data := data[ino := File.emptyDir];
      assert Valid_dirent_at(ino, fs.data) by {
        Dirents.zero_enc();
      }
      assert is_dir(ino);

      Dirents.zero_dir();
      assert is_dir(ino);
      mk_dir_type(ino);
      mk_data_at(ino);
      ValidData_change_one(ino);

      assert ValidRoot() by { reveal ValidRoot(); }
    }

    method {:timeLimitMultiplier 2} growInodeFor(txn: Txn, ghost d_ino: Ino, dents: MemDirents, ghost path: PathComp)
      returns (ok: bool)
      modifies Repr, dents.Repr(), dents.file.i.Repr
      requires ValidDirents(dents, d_ino)
      requires fs.has_jrnl(txn)
      requires dents.val.findName(path) >= |dents.val.s|
      requires dents.val.findFree() >= |dents.val.s|
      ensures fs.types_unchanged()
      ensures ok ==>
      && ValidDirents(dents, d_ino)
      && dents.val.findName(path) >= |dents.val.s|
      && dents.val.findFree() == old(dents.val.findFree())
      && dents.val.findFree() < |dents.val.s|
      && data == old(data)
      ensures fresh(dents.Repr() - old(dents.Repr()))
    {
      assert Repr !! dents.Repr();
      invert_dir(d_ino);
      assert Valid_dir_at(d_ino) by {
        get_data_at(d_ino);
      }

      ghost var val0 := dents.val;
      ok := dents.grow(txn);
      if !ok {
        return;
      }
      assert |fs.data[d_ino]| % 4096 == 0 by {
        dents.fs_ino_size();
      }
      val0.extend_zero_not_found(64, path);
      assert dents_ok:
        && dents.val.findName(path) >= |dents.val.s|
        && dents.val.findFree() == old(dents.val.findFree())
        && dents.val.findFree() < |dents.val.s|;

      dirents := dirents[d_ino := dents.val];
      assert data == old(data);
      assert is_dir(d_ino);
      assert is_of_type(d_ino, fs.types[d_ino]) by {
        assert fs.types[d_ino] == Inode.DirType;
        reveal is_of_type();
      }
      //assert Valid_dirent_at(d_ino, fs.data);
      mk_data_at(d_ino);
      ValidData_change_one(d_ino);
      assert ValidIno(d_ino, dents.file.i) by {
        dents.fs_valid_ino();
        assert ValidRoot() by { reveal ValidRoot(); }
      }
      reveal dents_ok;
    }

    // linkInodeAtFree inserts a new entry e' into d_ino
    //
    // requires caller to provide a free slot
    method linkInodeAtFree(txn: Txn, d_ino: Ino, dents: MemDirents, e': MemDirEnt, i: uint64)
      returns (ok: bool)
      modifies Repr, dents.Repr(), dents.file.i.Repr, e'.name
      requires e'.name != dents.file.bs
      requires i as nat == dents.val.findFree()
      requires i as nat < |dents.val.s|
      ensures ok ==> Valid()
      requires fs.has_jrnl(txn)
      requires ValidDirents(dents, d_ino) && e'.Valid()
      requires e'.used() && dents.val.findName(e'.path()) >= |dents.val.s|
      ensures ok ==>
      && data == old(
      var d0 := data[d_ino].dir;
      var d' := DirFile(d0[e'.path() := e'.ino]);
      data[d_ino := d'])
    {
      assert data[d_ino] == DirFile(dents.val.dir) by {
        get_data_at(d_ino);
      }

      assert data[d_ino] == DirFile(dents.val.dir) by {
        get_data_at(d_ino);
      }
      invert_dir(d_ino);

      assert e'.name != dents.file.bs && e'.name !in dents.file.i.Repr by {
        reveal dents.Valid();
      }
      ghost var path := e'.path();
      ghost var ino := e'.ino;
      ghost var d := dents.val.dir;
      ok := dents.insertEnt(txn, i, e');
      if !ok {
        return;
      }
      dents.fs_ino_size();
      //assert dents.file.ino == d_ino;
      dents.finish(txn);

      dirents := dirents[d_ino := dents.val];
      ghost var new_val := dents.val;
      ghost var d' := dents.val.dir;
      assert d' == d[path := ino];
      data := data[d_ino := DirFile(d')];
      assert is_dir(d_ino);
      assert fs.types[d_ino] == Inode.DirType;
      assert is_of_type(d_ino, fs.types[d_ino]) by { reveal is_of_type(); }
      mk_data_at(d_ino);
      ValidData_change_one(d_ino);
      assert ValidRoot() by { reveal ValidRoot(); }
    }

    // linkInode inserts a new entry e' into d_ino
    //
    // requires that e'.name is not already in the directory (in that case we
    // need to insert in a slightly different way that isn't implemented)
    method linkInode(txn: Txn, d_ino: Ino, dents: MemDirents, e': MemDirEnt)
      returns (ok: bool)
      modifies Repr, dents.Repr(), dents.file.i.Repr, e'.name
      requires e'.name != dents.file.bs
      ensures ok ==> Valid()
      requires fs.has_jrnl(txn)
      requires ValidDirents(dents, d_ino) && e'.Valid()
      requires e'.used() && dents.val.findName(e'.path()) >= |dents.val.s|
      ensures ok ==>
      && data == old(
      var d0 := data[d_ino].dir;
      var d' := DirFile(d0[e'.path() := e'.ino]);
      data[d_ino := d'])
    {
      var sz := dents.dirSize();
      var i := dents.findFree(txn);
      if !(i < sz) {
        ok := growInodeFor(txn, d_ino, dents, e'.path());
        // could not make space
        if !ok {
          return;
        }
      }
      ok := linkInodeAtFree(txn, d_ino, dents, e', i);
    }

    method {:timeLimitMultiplier 2} CREATE(txn: Txn, d_ino: Ino, name: Bytes, sz: uint64)
      returns (r: Result<Ino>, ghost junk: seq<byte>)
      modifies Repr, name
      requires name.Valid()
      requires sz <= Inode.MAX_SZ_u64
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      ensures r.Ok? ==>
      (var ino := r.v;
      && is_pathc(old(name.data))
      && old(is_dir(d_ino))
      && old(is_invalid(ino))
      && |junk| == sz as nat
      && data == old(
        var d := data[d_ino].dir;
        var d' := DirFile(d[name.data := ino]);
        data[ino := ByteFile(junk)][d_ino := d'])
      )
    {
      var ok, ino := allocFile(txn);
      if !ok {
        r := Err(NoSpc);
        return;
      }
      var is_path := Pathc?(name);
      if !is_path {
        // could also have 0s in it but whatever
        r := Err(NameTooLong);
        return;
      }
      var dents :- readDirents(txn, d_ino);
      assert dirents_for(dents, d_ino);
      assert fresh(dents.file.bs) by {
        assert dents.file.bs in dents.Repr();
      }
      assert ino_ok: ino !in old(data);
      var name_opt := dents.findName(txn, name);
      if name_opt.Some? {
        // TODO: support creating a file and overwriting existing (rather than
        // failing here)
        r := Err(Exist);
        return;
      }
      // TODO: somehow this block of assertions speeds up the proof, even though
      // they should just be a copy of the linkInode precondition
      var e' := MemDirEnt(name, ino);
      assert is_dir(d_ino);
      assert e'.Valid() && e'.used();
      assert dents.val.findName(e'.path()) == |dents.val.s|;
      assert ValidDirents(dents, d_ino);
      assert fs.has_jrnl(txn);

      //assert dents.Repr() !! Repr;
      // NOTE(tej): when e.name was missing from this method's modifies clause,
      // this just kept timing out rather than reporting a modifies clause error
      ok := linkInode(txn, d_ino, dents, e');
      if !ok {
        r := Err(NoSpc);
        return;
      }
      junk := [];
      if sz > 0 {
        var unused_r;
        unused_r, junk :- SETATTRsize(txn, ino, sz);
        assert ByteFs.ByteFilesys.setSize_with_junk([], sz as nat, junk) == junk;
      }
      // assert data == old(data[ino := File.empty][d_ino := DirFile(d')]);
      reveal ino_ok;
      r := Ok(ino);
      return;
    }

    method GETATTR(txn: Txn, ino: Ino)
      returns (r: Result<Attributes>)
      modifies fs.fs.fs.fs
      requires Valid() ensures Valid()
      requires fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> ino !in data
      ensures r.Ok? ==>
          (var attrs := r.v;
          && ino in data
          && attrs.is_dir == data[ino].DirFile?
          && data[ino].ByteFile? ==> attrs.size as nat == |data[ino].data|
          && data[ino].DirFile? ==> attrs.size as nat == 4096
          )
    {
      var ok, i := fs.startInode(txn, ino);
      if !ok {
        assert is_invalid(ino) by { reveal is_of_type(); }
        return Err(BadHandle);
      }
      if i.ty.DirType? {
        assert is_dir(ino) by { reveal is_of_type(); }
        //var dents := readDirentsInode(txn, ino, i);
        fs.finishInodeReadonly(ino, i);
        // NOTE: not sure what the size of a directory is supposed to be, so
        // just return its encoded size in bytes
        var attrs := Attributes(true, 4096);
        return Ok(attrs);
      }
      // is a file
      assert i.ty.FileType?;
      assert is_file(ino) by { reveal is_of_type(); }
      fs.finishInodeReadonly(ino, i);
      var attrs := Attributes(false, i.sz);
      return Ok(attrs);
    }

    method SETATTRsize(txn: Txn, ino: Ino, sz: uint64)
      returns (r:Result<()>, ghost junk: seq<byte>)
      modifies Repr
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> ino !in data
      ensures r.ErrIsDir? ==> is_dir(ino)
      ensures r.Ok? ==>
      && old(is_file(ino))
      && (var d0 := old(data[ino].data);
        var d' := ByteFs.ByteFilesys.setSize_with_junk(d0, sz as nat, junk);
        && (sz as nat > |d0| ==> |junk| == sz as nat - |d0|)
        && data == old(data[ino := ByteFile(d')]))
    {
      junk := [];
      if sz > Inode.MAX_SZ_u64 {
        r := Err(FBig);
        return;
      }
      var i :- openFile(txn, ino);
      assert dirents == old(dirents);
      invert_file(ino);
      ghost var d0: seq<byte> := old(fs.data[ino]);
      assert d0 == old(data[ino].data) by {
        get_data_at(ino);
      }

      fs.inode_metadata(ino, i);
      assert this !in fs.Repr;

      junk := fs.setSize(txn, ino, i, sz);
      fs.finishInode(txn, ino, i);

      ghost var d' := ByteFs.ByteFilesys.setSize_with_junk(d0, sz as nat, junk);
      data := data[ino := ByteFile(d')];

      assert Valid() by {
        file_change_valid(ino, d');
      }

      r := Ok(());
      return;
    }

    method openFile(txn: Txn, ino: Ino)
      returns (r:Result<MemInode>)
      modifies fs.fs.fs.fs
      requires Valid()
      requires fs.has_jrnl(txn)
      ensures r.Ok? ==>
      && fresh(r.v.Repr)
      && ValidIno(ino, r.v)
      && fs.inode_unchanged(ino, r.v.val())
      && is_file(ino)
      && old(is_file(ino))
      ensures !r.Ok? ==> Valid()
      ensures fs.data == old(fs.data)
      ensures r.ErrBadHandle? ==> is_invalid(ino)
      ensures r.ErrIsDir? ==> is_dir(ino)
      ensures r.Err? ==> r.err.BadHandle? || r.err.IsDir?
      ensures unchanged(this)
      ensures dirents == old(dirents)
    {
      var ok, i := fs.startInode(txn, ino);
      if !ok {
        assert is_invalid(ino) by { reveal is_of_type(); }
        return Err(BadHandle);
      }
      if i.ty.DirType? {
        assert is_dir(ino) by { reveal is_of_type(); }
        fs.finishInodeReadonly(ino, i);
        // assert ValidFiles() by { reveal ValidFiles(); }
        return Err(IsDir);
      }
      assert old(is_file(ino)) && is_file(ino) by { reveal is_of_type(); }
      return Ok(i);
    }

    twostate lemma file_change_valid(ino: Ino, d': seq<byte>)
      requires old(Valid()) && fs.Valid()
      requires old(is_file(ino))
      requires fs.data == old(fs.data[ino := d'])
      requires fs.types_unchanged()
      requires dirents == old(dirents)
      requires data == old(data[ino := ByteFile(d')])
      ensures Valid()
    {
      assert old(this).is_of_type(ino, old(fs.types)[ino]) by {
        reveal is_of_type();
      }
      assert is_of_type(ino, fs.types[ino]) by {
        assert is_file(ino);
        reveal is_of_type();
      }
      mk_data_at(ino);
      ValidData_change_one(ino);
      assert ValidRoot() by { reveal ValidRoot(); }
    }

    // TODO: add support for writes to arbitrary offsets
    method WRITE(txn: Txn, ino: Ino, off: uint64, bs: Bytes)
      returns (r: Result<()>)
      modifies Repr, bs
      requires Valid()
      // nothing to say in error case (need to abort)
      ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      requires 0 < |bs.data| <= 6*4096
      ensures r.ErrBadHandle? ==> ino !in old(data)
      ensures (r.Err? && r.err.Inval?) ==> ino in old(data) && old(data[ino].DirFile?)
      ensures r.Ok? ==>
      && ino in old(data) && old(data[ino].ByteFile?)
      && off as nat <= old(|data[ino].data|)
      && data == old(
      var d := data[ino].data;
      var d' := ByteFs.write_data(d, off as nat, bs.data);
      data[ino := ByteFile(d')])
    {
      var i_r := openFile(txn, ino);
      var i :- i_r.IsDirToInval();
      assert dirents == old(dirents);
      invert_file(ino);
      assert ValidIno(ino, i);
      ghost var d0: seq<byte> := old(fs.data[ino]);
      assert d0 == old(data[ino].data) by {
        get_data_at(ino);
      }
      if i.sz + bs.Len() > Inode.MAX_SZ_u64 {
        return Err(FBig);
      }
      if off > i.sz {
        // unsupported: creates a hole
        return Err(ServerFault);
      }
      fs.inode_metadata(ino, i);
      assert this !in fs.Repr;
      var ok;
      ok := fs.write(txn, ino, i, off, bs);
      if !ok {
        return Err(NoSpc);
      }

      fs.finishInode(txn, ino, i);

      ghost var f' := ByteFile(fs.data[ino]);
      data := data[ino := f'];

      assert Valid() by {
        file_change_valid(ino, f'.data);
      }
      return Ok(());
    }

    method {:timeLimitMultiplier 2} WRITEgeneral(txn: Txn, ino: Ino, off: uint64, bs: Bytes)
      returns (r: Result<()>)
      modifies Repr, bs
      requires Valid()
      requires fs.has_jrnl(txn)
      requires 0 < |bs.data| <= 6*4096
      // nothing to say in error case (need to abort)
      ensures r.Ok? ==> Valid()
    {
      var i_r := openFile(txn, ino);
      var i :- i_r.IsDirToInval();
      assert dirents == old(dirents);
      invert_file(ino);
      assert ValidIno(ino, i);
      ghost var d0: seq<byte> := old(fs.data[ino]);
      assert d0 == old(data[ino].data) by {
        get_data_at(ino);
      }
      if i.sz + bs.Len() > Inode.MAX_SZ_u64 ||
        sum_overflows(off, bs.Len()) ||
        off + bs.Len() > Inode.MAX_SZ_u64 {
        return Err(FBig);
      }
      if off > i.sz {
        fs.inode_metadata(ino, i);
        // unverified (because we should set this to zeros)
        ghost var junk := fs.setSize(txn, ino, i, off);
        assert |fs.data[ino]| == off as nat;
      }
      fs.inode_metadata(ino, i);
      assert this !in fs.Repr;
      var ok;
      ok := fs.write(txn, ino, i, off, bs);
      if !ok {
        return Err(NoSpc);
      }

      fs.finishInode(txn, ino, i);

      ghost var f' := ByteFile(fs.data[ino]);
      data := data[ino := f'];

      assert Valid() by {
        file_change_valid(ino, f'.data);
      }
      return Ok(());
    }

    method READ(txn: Txn, ino: Ino, off: uint64, len: uint64)
      returns (r: Result<ReadResult>)
      modifies fs.fs.fs.fs
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> ino !in data
      ensures r.ErrInval? ==> ino in data && data[ino].DirFile?
      ensures unchanged(this)
      ensures r.Ok? ==>
      (var bs := r.v.data;
       var eof := r.v.eof;
      && ino in data && data[ino].ByteFile?
      && is_read_data(data[ino].data, off as nat, len as nat, bs.data, eof)
      )
    {
      if len > 4096 {
        // we should really return a short read
        var bs := NewBytes(0);
        return Err(ServerFault);
      }
      var i_r := openFile(txn, ino);
      var i :- i_r.IsDirToInval();
      var bs, ok, eof := fs.read(txn, ino, i, off, len);
      fs.finishInodeReadonly(ino, i);
      if !ok {
        // TODO: this now only happens if the offset if completely
        // out-of-bounds, which I'm not sure we're supposed to handle
        return Err(ServerFault);
      }
      get_data_at(ino);
      assert Valid() by {
        assert ValidData() by {
          reveal Valid_data_at();
        }
      }
      return Ok(ReadResult(bs, eof));
    }

    method {:timeLimitMultiplier 2} MKDIR(txn: Txn, d_ino: Ino, name: Bytes)
      returns (r: Result<Ino>)
      modifies Repr, name
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      requires name.Valid()
      ensures (r.Err? && r.err.Exist?) ==>
      && old(is_dir(d_ino))
      && is_pathc(name.data)
      && name.data in old(data[d_ino].dir)
      ensures r.Ok? ==>
      (var ino := r.v;
      && old(is_dir(d_ino))
      && old(is_invalid(ino))
      && old(is_pathc(name.data))
      && data == old(
        var d := data[d_ino].dir;
        var d' := DirFile(d[name.data := ino]);
        data[ino := File.emptyDir][d_ino := d'])
      )
    {
      var is_path := Pathc?(name);
      if !is_path {
        // could also have 0s in it but whatever
        return Err(NameTooLong);
      }
      var ok, ino := allocDir(txn);
      if !ok {
        return Err(NoSpc);
      }
      // we allocate before reading d_ino because readDirents keeps the
      // directory open; if the caller guesses the newly-allocated directory, we
      // should fail
      if d_ino == ino {
        return Err(Inval);
      }

      var dents :- readDirents(txn, d_ino);
      assert dents.Repr() !! Repr;
      assert name !in Repr;
      assert ino != d_ino;
      //assert is_dir(d_ino);
      get_data_at(d_ino);
      var name_opt := dents.findName(txn, name);
      if name_opt.Some? {
        dents.val.findName_found(name.data);
        return Err(Exist);
      }
      dents.val.findName_not_found(name.data);

      var e' := MemDirEnt(name, ino);
      assert name.data == old(name.data);
      assert dents.Valid() && e'.Valid() && e'.used();
      ok := linkInode(txn, d_ino, dents, e');
      if !ok {
        return Err(NoSpc);
      }
      return Ok(ino);
    }

    method LOOKUP(txn: Txn, d_ino: Ino, name: Bytes)
      returns (r:Result<Ino>)
      modifies fs.fs.fs.fs
      requires Valid() ensures Valid()
      requires fs.has_jrnl(txn)
      requires name.Valid()
      ensures r.ErrBadHandle? ==> d_ino !in data
      ensures r.ErrNoent? ==> is_dir(d_ino) && name.data !in data[d_ino].dir
      ensures r.Ok? ==>
      (var ino := r.v;
      && is_pathc(name.data)
      && is_dir(d_ino)
      && name.data in data[d_ino].dir && data[d_ino].dir[name.data] == ino && ino != 0
      )
    {
      var path_ok := Pathc?(name);
      if !path_ok {
        return Err(NameTooLong);
      }
      var dents :- readDirents(txn, d_ino);
      assert DirFile(dents.dir()) == data[d_ino] by {
        get_data_at(d_ino);
      }
      assert name != dents.file.bs by {
        assert dents.file.bs in dents.Repr();
      }
      var name_opt := dents.findName(txn, name);
      dents.finishReadonly();
      if name_opt.None? {
        return Err(Noent);
      }
      var ino: Ino := name_opt.x.1;
      dents.val.findName_found(name.data);
      return Ok(ino);
    }

    // this is a low-level function that deletes an inode (currently restricted
    // to files) from the tree
    method removeInode(txn: Txn, ino: Ino)
      returns (r: Result<()>)
      modifies Repr
      requires Valid() ensures Valid()
      requires fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> is_invalid(ino) && data == old(data) == old(map_delete(data, ino))
      ensures r.ErrIsDir? ==> is_dir(ino) && data == old(data) && dirents == old(dirents)
      ensures r.Err? ==> r.err.BadHandle? || r.err.IsDir?
      ensures r.Ok? ==>
      && old(is_file(ino))
      && data == old(map_delete(data, ino))
      && dirents == old(dirents)
    {
      var ok, i := fs.startInode(txn, ino);
      if !ok {
        assert is_invalid(ino) by { reveal is_of_type(); }
        Std.map_delete_id(data, ino);
        return Err(BadHandle);
      }
      if i.ty == Inode.DirType {
        assert is_dir(ino) by { reveal is_of_type(); }
        fs.finishInodeReadonly(ino, i);
        return Err(IsDir);
      }
      assert is_file(ino) by { reveal is_of_type(); }
      fs.freeInode(txn, ino, i);
      //map_delete_not_in(data, ino);
      data := map_delete(data, ino);

      assert dirents == old(dirents);
      mk_invalid_type(ino);
      mk_data_at(ino);
      ValidData_change_one(ino);
      assert ValidRoot() by { reveal ValidRoot(); }
      return Ok(());
    }

    method unlinkInodeAt(txn: Txn, d_ino: Ino, dents: MemDirents, name: Bytes,
      // i and ino are the result of a succesfull findName call
      i: uint64, ghost ino: Ino)
      returns (r: Result<()>)
      modifies Repr, dents.Repr(), dents.file.i.Repr
      requires fs.has_jrnl(txn)
      requires is_pathc(name.data)
      requires name != dents.file.bs
      requires ValidDirents(dents, d_ino) ensures r.Ok? ==> Valid()
      requires
      // findName postcondition (when Some((i, ino)))
      && dents.val.findName(name.data) == i as nat
      && i as nat < |dents.val.s|
      && name.data in dents.val.dir
      && dents.val.dir[name.data] == ino
      ensures r.Err? ==> r.err.NoSpc?
      ensures name.data == old(name.data)
      ensures r.Ok? ==>
      && old(name.data in data[d_ino].dir)
      && data ==
        (var d0 := old(data[d_ino].dir);
        var d' := map_delete(d0, old(name.data));
        old(data)[d_ino := DirFile(d')])
    {
      ghost var path := name.data;
      invert_dir(d_ino);
      assert DirFile(dents.dir()) == data[d_ino] by {
        get_data_at(d_ino);
      }
      ghost var d0: Directory := old(data[d_ino].dir);

      assert ino_ok: path in d0 && ino == d0[path] by {
        dents.val.findName_found(path);
      }

      var ok := dents.deleteAt(txn, i);
      if !ok {
        return Err(NoSpc);
      }
      assert |fs.data[d_ino]| % 4096 == 0 by {
        dents.fs_ino_size();
      }
      dents.finish(txn);

      dirents := dirents[d_ino := dents.val];
      ghost var d': Directory := dents.val.dir;
      assert d' == map_delete(d0, path);
      data := data[d_ino := DirFile(d')];

      assert is_dir(d_ino);
      assert is_of_type(d_ino, fs.types[d_ino]) by { reveal is_of_type(); }
      mk_data_at(d_ino);
      ValidData_change_one(d_ino);
      assert Valid() by {
        assert ValidRoot() by { reveal ValidRoot(); }
      }
      reveal ino_ok;
      return Ok(());
    }

    method unlinkInode(txn: Txn, d_ino: Ino, dents: MemDirents, name: Bytes)
      returns (r: Result<Ino>)
      modifies Repr, dents.Repr(), dents.file.i.Repr
      requires fs.has_jrnl(txn)
      requires is_pathc(name.data)
      requires name != dents.file.bs
      requires ValidDirents(dents, d_ino) ensures r.Ok? ==> Valid()
      ensures r.ErrNoent? ==> name.data !in old(data[d_ino].dir)
      ensures r.Err? ==> r.err.Noent? || r.err.NoSpc?
      ensures r.Ok? ==>
      && old(name.data in data[d_ino].dir)
      && r.v == old(data[d_ino].dir[name.data])
      && data ==
        (var d0 := old(data[d_ino].dir);
        var d' := map_delete(d0, old(name.data));
        old(data)[d_ino := DirFile(d')])
    {
      ghost var path := name.data;
      assert dents.Repr() !! Repr;

      assert DirFile(dents.dir()) == data[d_ino] by {
        get_data_at(d_ino);
      }
      var name_opt := dents.findName(txn, name);
      if name_opt.None? {
        return Err(Noent);
      }

      var i := name_opt.x.0;
      var ino := name_opt.x.1;

      var _ :- unlinkInodeAt(txn, d_ino, dents, name, i, ino);
      return Ok(ino);
    }

    method unlink(txn: Txn, d_ino: Ino, name: Bytes)
      returns (r: Result<Ino>)
      modifies Repr
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      requires is_pathc(name.data)
      ensures r.ErrBadHandle? ==> d_ino !in old(data)
      ensures r.ErrNoent? ==> old(is_dir(d_ino)) && name.data !in old(data[d_ino].dir)
      ensures r.ErrNotDir? ==> old(is_file(d_ino))
      ensures !r.ErrIsDir?
      ensures r.Ok? ==>
      && old(is_dir(d_ino))
      && name.data in old(data[d_ino].dir)
      && r.v == old(data[d_ino].dir[name.data])
      && data ==
        (var d0 := old(data[d_ino].dir);
        var d' := map_delete(d0, old(name.data));
        old(data)[d_ino := DirFile(d')])
    {
      ghost var path := name.data;
      var dents :- readDirents(txn, d_ino);
      assert old(is_dir(d_ino));
      assert fresh(dents.file.bs) by {
        assert dents.file.bs in dents.Repr();
      }
      r := unlinkInode(txn, d_ino, dents, name);
    }

    method REMOVE(txn: Txn, d_ino: Ino, name: Bytes)
      returns (r: Result<()>)
      modifies Repr
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      requires name.Valid()
      ensures r.ErrBadHandle? ==> d_ino !in old(data)
      ensures r.ErrNoent? ==>
      && old(is_dir(d_ino))
      && is_pathc(name.data)
      && name.data !in old(data[d_ino].dir)
      ensures r.ErrIsDir? ==>
      && old(d_ino in data && data[d_ino].DirFile?)
      && is_pathc(name.data)
      && old(name.data) in old(data[d_ino].dir)
      && (var ino := old(data[d_ino].dir[name.data]);
        && ino in old(data)
        && old(data[ino].DirFile?))
      ensures r.Ok? ==>
      && old(is_dir(d_ino))
      && is_pathc(name.data)
      && name.data in old(data[d_ino].dir)
      && data ==
        (var d0 := old(data[d_ino].dir);
        var d' := map_delete(d0, old(name.data));
        map_delete(old(data)[d_ino := DirFile(d')], d0[old(name.data)]))
    {
      var path_ok := Pathc?(name);
      if !path_ok {
        return Err(NameTooLong);
      }
      var ino :- this.unlink(txn, d_ino, name);

      var remove_r := removeInode(txn, ino);

      if remove_r.ErrBadHandle? {
        return Ok(());
      }

      if remove_r.Err? {
        assert remove_r.ErrIsDir?;
        return Err(IsDir);
      }

      return Ok(());
    }

    // TODO: would be nice to combine this with removeInode; best way might be
    // to require caller to do the startInode/type checking and only implement
    // the removal part
    method removeInodeDir(txn: Txn, ino: Ino)
      modifies Repr
      requires Valid() ensures Valid()
      requires ino != rootIno
      requires is_dir(ino)
      requires fs.has_jrnl(txn)
      ensures data == old(map_delete(data, ino))
      ensures dirents == old(map_delete(dirents, ino))
    {
      var ok, i := fs.startInode(txn, ino);
      if !ok {
        assert is_invalid(ino) by { reveal is_of_type(); }
        assert false;
      }
      fs.freeInode(txn, ino, i);
      data := map_delete(data, ino);
      dirents := map_delete(dirents, ino);

      mk_invalid_type(ino);
      mk_data_at(ino);
      ValidData_change_one(ino);
      assert ValidRoot() by { reveal ValidRoot(); }
    }

    method RMDIR(txn: Txn, d_ino: Ino, name: Bytes)
      returns (r: Result<()>)
      modifies Repr
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      requires name.Valid()
      ensures r.ErrBadHandle? ==> d_ino !in old(data)
      ensures r.ErrNoent? ==>
      && old(is_dir(d_ino))
      && is_pathc(name.data)
      && name.data !in old(data[d_ino].dir)
      ensures r.ErrNotDir? ==>
      && is_pathc(name.data)
      && (old(is_file(d_ino))
        || (&& old(d_ino in data && data[d_ino].DirFile?)
          && old(name.data) in old(data[d_ino].dir)
          && (var ino := old(data[d_ino].dir[name.data]);
            && ino in old(data)
            && old(data[ino].ByteFile?))))
      ensures r.Ok? ==>
      && old(is_dir(d_ino))
      && is_pathc(name.data)
      && name.data in old(data[d_ino].dir)
      && data ==
        (var d0 := old(data[d_ino].dir);
        var d' := map_delete(d0, old(name.data));
        map_delete(old(data)[d_ino := DirFile(d')], d0[old(name.data)]))
    {
      var path_ok := Pathc?(name);
      if !path_ok {
        return Err(NameTooLong);
      }
      var ino :- this.unlink(txn, d_ino, name);
      if ino == rootIno {
        return Err(Inval);
      }
      var dents_r := readDirents(txn, ino);
      if dents_r.ErrBadHandle? {
        Std.map_delete_id(data, ino);
        return Ok(());
      }
      if dents_r.ErrNotDir? {
        return Err(NotDir);
      }
      assert dents_r.Ok?;
      var dents := dents_r.v;
      var is_empty := dents.isEmpty(txn);
      dents.finishReadonly();
      if !is_empty {
        get_data_at(ino);
        assert data[ino].dir != map[];
        return Err(NotEmpty);
      }

      removeInodeDir(txn, ino);

      return Ok(());
    }

    method READDIR(txn: Txn, d_ino: Ino)
      returns (r: Result<seq<MemDirEnt>>)
      modifies fs.fs.fs.fs
      requires Valid() ensures Valid()
      requires fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> d_ino !in data
      ensures r.Ok? ==>
      (var dents_seq := r.v;
      && mem_seq_valid(dents_seq)
      && fresh(mem_dirs_repr(dents_seq))
      && d_ino in data
      && data[d_ino].DirFile?
      && seq_to_dir(mem_seq_val(dents_seq)) == data[d_ino].dir
      && |dents_seq| == |data[d_ino].dir|
      )
    {
      var dents :- readDirents(txn, d_ino);
      assert DirFile(dents.dir()) == data[d_ino] by {
        get_data_at(d_ino);
      }
      assert fresh(dents.file) by {
        assert dents.file in dents.Repr();
      }
      var dents_seq := dents.usedDents(txn);
      dents.finishReadonly();
      return Ok(dents_seq);
    }

    method {:timeLimitMultiplier 2} readWithNameFree(txn: Txn, d_ino: Ino, name: Bytes)
      returns (r: Result<MemDirents>)
      modifies Repr
      requires fs.has_jrnl(txn)
      requires is_pathc(name.data)
      requires Valid()
      ensures r.ErrBadHandle? ==> is_invalid(d_ino)
      ensures r.ErrNotDir? ==> is_file(d_ino)
      ensures name.data == old(name.data)
      ensures r.Ok? ==>
      && dirents_for(r.v, d_ino)
      && r.v.val.findName(name.data) == |r.v.val.s|
      && r.v.file.bs != name
    {
      var dents :- readDirents(txn, d_ino);
      assert name != dents.file.bs by {
        assert dents.file.bs in dents.Repr();
      }
      assert fresh(dents.file) by {
        assert dents.file in dents.Repr();
      }
      var name_opt := dents.findName(txn, name);
      if name_opt.None? {
        return Ok(dents);
      }
      var i := name_opt.x.0;
      var dst_ino := name_opt.x.1;
      var _ :- unlinkInodeAt(txn, d_ino, dents, name, i, dst_ino);

      // need to re-confirm that name was removed since unlink's postcondition
      // isn't strong enough
      dents :- assert readDirents(txn, d_ino);

      assert fresh(dents.file.Repr()) by {
        assert dents.file.Repr() <= dents.Repr();
      }

      name_opt := dents.findName(txn, name);
      if name_opt.Some? {
        return Err(ServerFault);
      }
      return Ok(dents);
    }

    method {:timeLimitMultiplier 2} renamePaths(txn: Txn, src_d_ino: Ino, src_name: Bytes, dst_d_ino: Ino, dst_name: Bytes)
      returns (r: Result<()>)
      modifies Repr, dst_name
      requires is_pathc(src_name.data) && is_pathc(dst_name.data)
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
    {
      var ino :- unlink(txn, src_d_ino, src_name);
      if ino == 0 {
        return Err(Inval);
      }
      var dst :- readWithNameFree(txn, dst_d_ino, dst_name);
      assert dst_name != dst.file.bs by {
        assert dst.file.bs in dst.Repr();
      }
      var e' := MemDirEnt(dst_name, ino);
      var ok := linkInode(txn, dst_d_ino, dst, e');
      if !ok {
        return Err(NoSpc);
      }
      return Ok(());
    }

    method RENAME(txn: Txn, src_d_ino: Ino, src_name: Bytes, dst_d_ino: Ino, dst_name: Bytes)
      returns (r: Result<()>)
      modifies Repr, dst_name
      requires src_name.Valid() && dst_name.Valid()
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      // TODO: need to write down the spec
    {
      var src_name_ok := Pathc?(src_name);
      if !src_name_ok {
        return Err(NameTooLong);
      }
      var dst_name_ok := Pathc?(dst_name);
      if !dst_name_ok {
        return Err(NameTooLong);
      }
      var _ :- renamePaths(txn, src_d_ino, src_name, dst_d_ino, dst_name);
      return Ok(());
    }

  }
}
