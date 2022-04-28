include "typed_fs.dfy"
include "dir/mem_dirent.dfy"
include "nfs.s.dfy"
include "../machine/time.s.dfy"
include "../util/lock_order.dfy"
include "../util/bytes.dfy"

module DirFs
{
  import opened Std
  import opened Machine
  import opened ByteSlice
  import opened InodeFs
  import opened FsKinds
  import opened JrnlTypes
  import opened JrnlSpec

  import opened LockOrder
  import opened DirEntries
  import opened MemDirEnts
  import opened MemDirEntries
  import opened Paths
  import opened TypedFs
  import opened FileCursor
  import opened MemInodes
  import ByteHelpers
  import Time
  import Inode

  import opened Nfs

  import C = Collections

  type FsData = map<Ino, seq<byte>>
  type FsAttrs = map<Ino, Inode.Attrs>

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
      print "failed to commit\n";
      return Err(ServerFault);
    }
    return r;
  }

  // returns Ok(ino) if ino_ok(ino) (in which case ino is an Ino)
  method checkInoBounds(ino: uint64) returns (r:Result<Ino>)
    ensures r.Err? ==> !ino_ok(ino) && r.ErrBadHandle?
    ensures r.Ok? ==> r.v == ino
  {
    var ok := is_ino_ok(ino);
    if !ok {
      return Err(BadHandle);
    }
    return Ok(ino);
  }

  method serverTime() returns (t:Inode.NfsTime)
  {
    var unix_nano := Time.TimeUnixNano();
    var sec := unix_nano / 1_000_000_000;
    var nsec := unix_nano % 1_000_000_000;
    return Inode.NfsTime((sec % 0x1_0000_0000) as uint32, nsec as uint32);
  }

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

    static function method oneIno(): Ino {
      reveal ino_ok();
      1 as Ino
    }

    static const rootIno: Ino := oneIno();

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
      requires fs.types[ino].ty == Inode.DirType
      ensures is_of_type(ino, fs.types[ino].ty)
    {
      reveal is_of_type();
    }

    lemma mk_file_type(ino: Ino)
      requires fs.Valid()
      requires is_file(ino)
      requires fs.types[ino].ty == Inode.FileType
      ensures is_of_type(ino, fs.types[ino].ty)
    {
      reveal is_of_type();
    }

    lemma mk_invalid_type(ino: Ino)
      requires fs.Valid()
      requires is_invalid(ino)
      requires fs.types[ino].ty == Inode.InvalidType
      ensures is_of_type(ino, fs.types[ino].ty)
    {
      reveal is_of_type();
    }

    predicate ValidTypes()
      reads this, fs
      requires fs.ValidDomains()
    {
      forall ino: Ino :: is_of_type(ino, fs.types[ino].ty)
    }

    lemma invert_dir(ino: Ino)
      requires fs.ValidDomains()
      requires ValidTypes()
      requires is_dir(ino)
      ensures fs.types[ino].ty == Inode.DirType
    {
      reveal is_of_type();
      ghost var t := fs.types[ino].ty;
      assert is_of_type(ino, t);
      if t == Inode.InvalidType {}
      else if t == Inode.FileType {}
      else if t == Inode.DirType {}
    }

    lemma invert_file(ino: Ino)
      requires fs.ValidDomains()
      requires ValidTypes()
      requires is_file(ino)
      ensures fs.types[ino].ty == Inode.FileType
    {
      reveal is_of_type();
      ghost var t := fs.types[ino].ty;
      assert is_of_type(ino, t);
      if t == Inode.InvalidType {}
      else if t == Inode.FileType {}
      else if t == Inode.DirType {}
    }

    lemma data_to_is_dir(ino: Ino)
      requires fs.ValidDomains()
      requires ValidTypes()
      requires ino in data && data[ino].DirFile?
      ensures is_dir(ino)
    {
      reveal is_of_type();
      ghost var t := fs.types[ino].ty;
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

    predicate Valid_file_at(ino: Ino, fsdata: FsData, attrs: FsAttrs)
      reads this
      requires ino_dom(fsdata) && ino_dom(attrs)
    {
      is_file(ino) ==> this.data[ino] == ByteFile(fsdata[ino], attrs[ino])
    }

    predicate Valid_dir_at(ino: Ino, attrs: FsAttrs)
      reads this
      requires ino_dom(attrs)
    {
      is_dir(ino) ==> this.data[ino] == DirFile(dirents[ino].dir, attrs[ino])
    }

    predicate Valid_invalid_at(ino: Ino, fsdata: FsData)
      requires ino_dom(fsdata)
      reads this
    {
      is_invalid(ino) ==> fsdata[ino] == []
    }

    predicate {:opaque} Valid_data_at(ino: Ino, fsdata: FsData, fsattrs: FsAttrs)
      requires ino_dom(fsdata)
      requires ino_dom(fsattrs)
      reads this
    {
        && Valid_dirent_at(ino, fsdata)
        && Valid_file_at(ino, fsdata, fsattrs)
        && Valid_dir_at(ino, fsattrs)
        && Valid_invalid_at(ino, fsdata)
    }

    predicate ValidData()
      requires fs.ValidDomains()
      reads this, fs
    {
      forall ino: Ino :: Valid_data_at(ino, fs.data, fs.types)
    }

    lemma get_data_at(ino: Ino)
      requires fs.ValidDomains() && ValidData()
      ensures Valid_dirent_at(ino, fs.data)
      ensures Valid_file_at(ino, fs.data, fs.types)
      ensures Valid_dir_at(ino, fs.types)
      ensures Valid_invalid_at(ino, fs.data)
    {
      reveal Valid_data_at();
      assert Valid_data_at(ino, fs.data, fs.types);
    }

    lemma mk_data_at(ino: Ino)
      requires fs.ValidDomains()
      requires Valid_dirent_at(ino, fs.data)
      requires Valid_file_at(ino, fs.data, fs.types)
      requires Valid_dir_at(ino, fs.types)
      requires Valid_invalid_at(ino, fs.data)
      ensures Valid_data_at(ino, fs.data, fs.types)
    {
      reveal Valid_data_at();
    }

    twostate lemma ValidData_change_one(ino: Ino)
      requires old(fs.ValidDomains()) && old(ValidData()) && old(ValidTypes())
      requires fs.ValidDomains()
      requires Valid_data_at(ino, fs.data, fs.types)
      requires is_of_type(ino, fs.types[ino].ty)
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
        ensures Valid_data_at(ino, fsdata, fs.types)
      {
        reveal Valid_data_at();
        assert old(Valid_data_at(ino, fsdata0, fs.types));
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

    constructor {:timeLimitMultiplier 2} Init(fs: TypedFilesys, ghost attrs0: Inode.Attrs)
      requires fs.Valid()
      requires attrs0.ty == Inode.DirType
      requires fs.data == map ino: Ino {:trigger} ::
                            if ino == rootIno
                            then Dirents.zero.enc() else []
      requires fs.types == map ino: Ino {:trigger} ::
                            if ino == rootIno
                            then attrs0
                            else Inode.Attrs.zero
      ensures Valid()
      ensures fresh(Repr - fs.Repr)
      ensures this.rootIno == rootIno
      ensures data == map[rootIno := DirFile(map[], attrs0)]
    {
      this.fs := fs;
      var dirents0 : map<Ino, Dirents> := map[rootIno := Dirents.zero];
      this.dirents := dirents0;
      this.data := map[rootIno := DirFile(map[], attrs0)];
      new;
      Dirents.zero_dir();
      assert ValidData() by {
        reveal Valid_data_at();
      }
      assert ValidRoot() by { reveal ValidRoot(); }
      assert ValidTypes() by { reveal is_of_type(); }
    }

    static method createRootDir(fs: TypedFilesys, txn: Txn, ino: Ino, attrs0: Inode.Attrs)
      returns (ok: bool)
      modifies fs.Repr
      requires fs.Valid() ensures ok ==> fs.Valid()
      requires fs.has_jrnl(txn)
      requires fs.types[ino].ty.InvalidType?
      requires attrs0.ty.DirType?
      requires fs.data[ino] == []
      ensures ok ==>
      && fs.data == old(fs.data[ino := Dirents.zero.enc()])
      && fs.types == old(fs.types[ino := attrs0])
    {
      var i := fs.allocateAt(txn, ino, Inode.DirType);
      ok := writeEmptyDirToFs(fs, txn, ino, i, attrs0);
    }

    // to avoid having to find the jrnl field in ops.go
    method Begin() returns (txn: Txn)
      requires Valid()
      ensures fs.has_jrnl(txn)
    {
      fs.reveal_valids();
      txn := fs.fs.fs.fs.jrnl.Begin();
    }

    static method New(d: Disk, uid: uint32, gid: uint32)
      returns (fs: Option<DirFilesys>, ghost attrs0: Inode.Attrs)
      ensures fs.Some? ==> fresh(fs.x.Repr) && fs.x.Valid()
      ensures fs.Some? ==>
        && has_root_attrs(attrs0, uid, gid)
        && fs.x.data == map[fs.x.rootIno := DirFile(map[], attrs0)]
    {
      var fs_ := new TypedFilesys.Init(d);

      fs_.reveal_valids();
      var txn := fs_.fs.fs.fs.jrnl.Begin();
      var attrs := RootAttrs(uid, gid);
      attrs0 := attrs;
      var ok := createRootDir(fs_, txn, rootIno, attrs);
      if !ok {
        fs := None;
        return;
      }
      fs_.reveal_valids();
      ok := txn.Commit();
      if !ok {
        fs := None;
        return;
      }
      assert fs_.Valid();

      var dir_fs := new DirFilesys.Init(fs_, attrs0);
      fs := Some(dir_fs);
    }

    constructor Recover(jrnl_: Jrnl, ghost fs: DirFilesys)
      requires fs.Valid()
      requires same_jrnl(jrnl_, fs.fs.fs.fs.fs.jrnl)
      ensures this.fs.fs.fs.fs.jrnl == jrnl_
      ensures this.data == fs.data
      ensures fresh(Repr - {jrnl_})
      ensures Valid()
    {
      this.fs := new TypedFilesys.Recover(jrnl_, fs.fs);
      this.dirents := fs.dirents;
      this.data := fs.data;

      new;
      forall ino: Ino
        ensures Valid_data_at(ino, this.fs.data, this.fs.types)
      {
        fs.get_data_at(ino);
        reveal Valid_data_at();
      }
      assert ValidData();
      assert ValidRoot() by { reveal ValidRoot(); }
      assert ValidTypes() by { reveal is_of_type(); }
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
      if i.ty().FileType? {
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

    method updateDirentsMtime(ghost d_ino: Ino, dents: MemDirents)
      returns (dir_attrs': Fattr3)
      modifies this, dents.file.ReprFs
      requires ValidDirents(dents, d_ino)
      ensures ValidDirents(dents, d_ino)
      ensures has_modify_attrs(old(data[d_ino].attrs), dir_attrs'.attrs)
      ensures dirents == old(dirents)
      ensures
      var d0 := data[d_ino].dir;
      var attrs' := dir_attrs'.attrs;
      data == old(data[d_ino := DirFile(d0, attrs')])
    {
      get_data_at(d_ino);
      var dir_attrs := dents.getAttrs();
      var dir_attrs_new := ModifyAttrs(dir_attrs);
      var dir_sz := dents.getSizeBytes();
      dir_attrs' := Fattr3(NFS3DIR, dir_sz, dir_attrs_new);
      dents.setAttrs(dir_attrs_new);
      ghost var d0 := data[d_ino].dir;
      data := data[d_ino := DirFile(d0, dir_attrs_new)];
      assert ValidIno(d_ino, dents.file.i) by {
        dents.fs_valid_ino();
        assert is_dir(d_ino);
        assert is_of_type(d_ino, fs.types[d_ino].ty) by {
          reveal is_of_type();
        }
        mk_data_at(d_ino);
        ValidData_change_one(d_ino);
        assert ValidRoot() by { reveal ValidRoot(); }
      }
    }


    // private
    //
    // creates a file disconnected from the file system (which is perfectly
    // legal but useless for most clients)
    method allocFile(txn: Txn, sz: uint64, attrs0: Inode.Attrs)
      returns (r:Result<Ino>)
      modifies Repr
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      requires sz as nat <= Inode.MAX_SZ
      requires attrs0.ty.FileType?
      ensures dirents == old(dirents)
      ensures r.Ok? ==>
      var ino := r.v;
      && old(is_invalid(ino))
      && ino != 0
      && data == old(data[ino := ByteFile(C.repeat(0 as byte, sz as nat), attrs0)])
    {
      var ok, ino, i := fs.allocInode(txn, Inode.FileType);
      if !ok {
        return Err(NoSpc);
      }
      fs.setAttrs(ino, i, attrs0);
      var setsize_r := fs.setSize(txn, ino, i, sz);
      if setsize_r.SetSizeNotZero? {
        return Err(JukeBox(sz));
      }
      if setsize_r.SetSizeNoSpc? {
        return Err(NoSpc);
      }
      assert this !in fs.Repr;
      fs.finishInode(txn, ino, i);
      assert old(is_invalid(ino)) by {
        assert old(is_of_type(ino, fs.types[ino].ty));
        reveal is_of_type();
      }
      data := data[ino := ByteFile(C.repeat(0 as byte, sz as nat), attrs0)];

      // NOTE(tej): this assertion takes far longer than I expected
      assert is_file(ino);
      mk_file_type(ino);
      mk_data_at(ino);
      ValidData_change_one(ino);

      assert ValidRoot() by { reveal ValidRoot(); }
      return Ok(ino);
    }

    static method writeEmptyDirToFs(fs: TypedFilesys, txn: Txn,
      ino: Ino, i: MemInode, attrs0: Inode.Attrs)
      returns (ok: bool)
      modifies fs.Repr, i.Repr
      requires fs.ValidIno(ino, i) ensures ok ==> fs.Valid()
      requires fs.has_jrnl(txn)
      requires fs.data[ino] == []
      requires attrs0.ty == fs.types[ino].ty
      ensures ok ==> fs.types == old(fs.types[ino := attrs0])
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
      fs.setAttrs(ino, i, attrs0);

      fs.finishInode(txn, ino, i);
    }

    // private
    //
    // creates a directory disconnected from the file system (which is perfectly
    // legal but useless for most clients)
    method {:timeLimitMultiplier 2} allocDir(txn: Txn, attrs0: Inode.Attrs)
      returns (ok: bool, ino: Ino)
      modifies Repr
      requires Valid() ensures ok ==> Valid()
      requires attrs0.ty.DirType?
      requires fs.has_jrnl(txn)
      ensures ok ==>
      && old(is_invalid(ino))
      && ino != 0
      && data == old(data[ino := DirFile(map[], attrs0)])
      && dirents == old(dirents[ino := Dirents.zero])
      && is_dir(ino)
    {
      var i;
      ok, ino, i := fs.allocInode(txn, Inode.DirType);
      if !ok {
        return;
      }
      assert old(is_invalid(ino)) by {
        assert old(is_of_type(ino, fs.types[ino].ty));
        reveal is_of_type();
      }

      assert this !in fs.Repr;
      ok := writeEmptyDirToFs(fs, txn, ino, i, attrs0);
      if !ok {
        return;
      }

      dirents := dirents[ino := Dirents.zero];
      data := data[ino := DirFile(map[], attrs0)];
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
      assert Valid_dir_at(d_ino, fs.types) by {
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
      assert is_of_type(d_ino, fs.types[d_ino].ty) by {
        assert fs.types[d_ino].ty == Inode.DirType;
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
      modifies Repr, dents.Repr(), dents.file.i.Repr
      requires e'.name != dents.file.bs
      requires e'.name !in dents.file.i.Repr
      requires i as nat == dents.val.findFree()
      requires i as nat < |dents.val.s|
      ensures ok ==> Valid()
      requires fs.has_jrnl(txn)
      requires ValidDirents(dents, d_ino) && e'.Valid()
      requires e'.used() && dents.val.findName(e'.path()) >= |dents.val.s|
      ensures ok ==>
      && data == old(
      var d0 := data[d_ino];
      var d' := DirFile(d0.dir[e'.path() := e'.ino], d0.attrs);
      data[d_ino := d'])
    {
      assert data[d_ino] == DirFile(dents.val.dir, fs.types[d_ino]) by {
        get_data_at(d_ino);
      }

      assert data[d_ino] == DirFile(dents.val.dir, fs.types[d_ino]) by {
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
      data := data[d_ino := DirFile(d', fs.types[d_ino])];
      assert is_dir(d_ino);
      assert fs.types[d_ino].ty == Inode.DirType;
      assert is_of_type(d_ino, fs.types[d_ino].ty) by { reveal is_of_type(); }
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
      modifies Repr, dents.Repr(), dents.file.i.Repr
      requires e'.name != dents.file.bs
      requires e'.name !in dents.file.i.Repr
      ensures ok ==> Valid()
      requires fs.has_jrnl(txn)
      requires ValidDirents(dents, d_ino) && e'.Valid()
      requires e'.used() && dents.val.findName(e'.path()) >= |dents.val.s|
      ensures ok ==>
      && data == old(
      var d0 := data[d_ino];
      var d' := DirFile(d0.dir[e'.path() := e'.ino], d0.attrs);
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
      assert e'.Valid() && e'.path() == old(e'.path()) by {
        assert e'.name !in dents.Repr();
        assert e'.name.data == old(e'.name.data);
      }
      ok := linkInodeAtFree(txn, d_ino, dents, e', i);
    }

    static method CreateAttributes(how: CreateHow3)
      returns (attrs:Inode.Attrs)
      ensures has_create_attrs(attrs, how)
    {
      if how.Exclusive? {
        return Inode.Attrs.zero_file;
      }
      var how_attrs := how.obj_attributes;
      var mode := how_attrs.mode.get_default(0644);
      var uid := how_attrs.uid.get_default(0);
      var gid := how_attrs.gid.get_default(0);
      var mtime := Inode.NfsTime(0, 0);
      if how_attrs.mtime.SetToClientTime? {
        mtime := how_attrs.mtime.time;
      } else
        // set an initial mtime even if client requests "DontChange" in CREATE
        if how_attrs.mtime.SetToServerTime? || how_attrs.mtime.DontChange? {
        mtime := serverTime();
      }
      return Inode.Attrs(Inode.FileType, mode, uid, gid, mtime);
    }

    static method validatePath(name: Bytes) returns (p: Result<()>)
      requires name.Valid()
      ensures p.Ok? ==> valid_name(name.data)
      ensures p.Err? ==> p.err.NameTooLong? || p.err.Inval?
    {
      var len := name.Len();
      if len > path_len_u64 {
        return Err(NameTooLong);
      }
      var pathc := Pathc?(name);
      if !pathc || len == 0 {
        print "invalid path ";
        name.Print();
        print "\n";
        return Err(Inval);
      }
      if len == 1 {
        var x0 := name.Get(0);
        if x0 == '.' as byte {
          assert name.data == ['.' as byte];
          return Err(Inval);
        }
      }
      assert name.data != ['.' as byte];
      if len == 2 {
        var x0 := name.Get(0);
        var x1 := name.Get(1);
        if x0 == '.' as byte && x1 == '.' as byte {
          assert name.data == ['.' as byte, '.' as byte];
          return Err(Inval);
        }
      }
      assert name.data != ['.' as byte, '.' as byte];
      return Ok(());
    }

    // public
    method {:timeLimitMultiplier 2} CREATE(txn: Txn, d_ino: uint64, name: Bytes, how: CreateHow3)
      returns (r: Result<CreateResult>)
      modifies Repr
      requires name.Valid()
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      ensures r.Ok? ==>
      && ino_ok(d_ino)
      && (var ino := r.v.ino;
       var fattrs := r.v.attrs;
       var file := ByteFile(C.repeat(0 as byte, how.size() as nat), fattrs.attrs);
      && valid_name(old(name.data))
      && old(is_dir(d_ino))
      && old(is_invalid(ino))
      && has_create_attrs(fattrs.attrs, how)
      && has_before_attrs(old(data[d_ino].attrs), r.v.dir_before)
      && has_modify_attrs(old(data[d_ino].attrs), r.v.dir_attrs.attrs)
      && is_file_attrs(file, fattrs)
      && (var dir_attrs := r.v.dir_attrs.attrs;
        data == old(
        var d0 := data[d_ino];
        var d' := DirFile(d0.dir[name.data := ino], dir_attrs);
        data[ino := file][d_ino := d']))
      )
    {
      var d_ino :- checkInoBounds(d_ino);
      var sz := how.size();
      if sz > Inode.MAX_SZ_u64 {
        r := Err(NoSpc);
        return;
      }
      var attrs := CreateAttributes(how);
      var ino :- allocFile(txn, sz, attrs);
      var _ :- validatePath(name);
      var dents :- readDirents(txn, d_ino);
      var before_sz := dents.getSizeBytes();
      var before_attrs := dents.getAttrs();
      var dir_before := BeforeAttr(before_sz, before_attrs.mtime);
      var dir_attrs := updateDirentsMtime(d_ino, dents);
      assert && ValidDirents(dents, d_ino)
            && fresh(dents.Repr())
            && fresh(dents.file.i.Repr);
      // assert dirents_for(dents, d_ino);
      assert fresh(dents.file.bs) by {
        assert dents.file.bs in dents.Repr();
      }
      assert ino_ok: ino !in old(data);
      var name_opt := dents.findName(txn, name);
      if name_opt.Some? {
        if how.Unchecked? {
          // TODO: support creating a file and overwriting existing (rather than
          // failing here)
          print "returning ERREXIST instead of overwriting\n";
          r := Err(Exist);
        } else {
          r := Err(Exist);
        }
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
      var ok := linkInode(txn, d_ino, dents, e');
      if !ok {
        r := Err(NoSpc);
        return;
      }
      reveal ino_ok;
      var fattrs := Fattr3(NFS3REG, sz, attrs);
      r := Ok(CreateResult(ino, fattrs, dir_before, dir_attrs));
      return;
    }

    method inodeFattr3(ghost ino: Ino, i: MemInode)
      returns (attr3: Fattr3)
      requires ValidIno(ino, i)
      requires ino in data
      ensures is_file_attrs(data[ino], attr3)
    {
      get_data_at(ino);
      fs.inode_metadata(ino, i);
      reveal is_of_type();
        // return the encoded size for a directory
      attr3 := Fattr3(if i.ty().DirType? then NFS3DIR else NFS3REG,
        i.sz,
        i.attrs);
    }

    method dirFattr3(ghost ino: Ino, dents: MemDirents)
      returns (attr3: Fattr3)
      requires ValidDirents(dents, ino)
      requires ino in data
      ensures is_file_attrs(data[ino], attr3)
    {
      attr3 := inodeFattr3(ino, dents.file.i);
    }

    // public
    method GETATTR(txn: Txn, ino: uint64)
      returns (r: Result<Fattr3>)
      modifies fs.fs.fs.fs
      requires Valid() ensures Valid()
      requires fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> ino !in data
      ensures r.Ok? ==>
          (var attrs := r.v;
          && ino in data
          && is_file_attrs(data[ino], attrs)
          )
    {
      var ino :- checkInoBounds(ino);
      var ok, i := fs.startInode(txn, ino);
      if !ok {
        assert is_invalid(ino) by { reveal is_of_type(); }
        return Err(BadHandle);
      }
      if i.ty().DirType? {
        assert is_dir(ino) by { reveal is_of_type(); }
        var attrs := inodeFattr3(ino, i);
        //var dents := readDirentsInode(txn, ino, i);
        fs.finishInodeReadonly(ino, i);
        return Ok(attrs);
      }
      // is a file
      assert i.ty().FileType?;
      assert is_file(ino) by { reveal is_of_type(); }
      var attrs := inodeFattr3(ino, i);
      fs.finishInodeReadonly(ino, i);
      return Ok(attrs);
    }

    static method SetattrAttributes(sattr: Sattr3, attrs0: Inode.Attrs)
      returns (attrs: Inode.Attrs)
      ensures has_set_attrs(attrs0, attrs, sattr)
    {
      var mode := sattr.mode.get_default(attrs0.mode);

      var uid := sattr.uid.get_default(attrs0.uid);
      var gid := sattr.gid.get_default(attrs0.gid);

      var mtime := attrs0.mtime;
      if sattr.mtime.SetToClientTime? {
        mtime := sattr.mtime.time;
      } else if sattr.mtime.SetToServerTime? {
        mtime := serverTime();
      }

      return Inode.Attrs(attrs0.ty, mode, uid, gid, mtime);
    }

    static method MkdirAttributes(sattr: Sattr3)
      returns (attrs: Inode.Attrs)
      ensures has_mkdir_attrs(attrs, sattr)
    {
      var sattr := sattr;
      if sattr.mtime.DontChange? {
        sattr := sattr.(mtime := SetToServerTime);
      }
      attrs := SetattrAttributes(sattr, Inode.Attrs.zero_dir);
    }

    method SETATTRdir(txn: Txn, ino: Ino, i: MemInode, attrs: Sattr3)
      returns (r:Result<()>, ghost attrs': Inode.Attrs)
      modifies Repr, i.Repr
      requires ValidIno(ino, i) ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      requires is_dir(ino)
      ensures r.ErrIsDir? ==> attrs.size.Some? && old(is_dir(ino))
      ensures !r.ErrBadHandle?
      ensures r.Ok? ==>
      && has_set_attrs(old(data[ino].attrs), attrs', attrs)
      && var d0 := old(data[ino]);
        data == old(data[ino := DirFile(d0.dir, attrs')])
    {
      if attrs.size.Some? {
        r := Err(IsDir);
        return;
      }
      var sz: uint64 := attrs.size.get_default(i.sz);
      assert dirents == old(dirents);
      ghost var old_dir := old(data[ino].dir);
      ghost var attrs0 := data[ino].attrs;
      ghost var d0 := old(fs.data[ino]);
      get_data_at(ino);

      fs.inode_metadata(ino, i);
      assert this !in fs.Repr;
      assert i.attrs == attrs0 by {
        get_data_at(ino);
      }

      var attrs'_val := SetattrAttributes(attrs, i.attrs);
      attrs' := attrs'_val;
      fs.setAttrs(ino, i, attrs'_val);
      fs.finishInode(txn, ino, i);

      data := data[ino := DirFile(old_dir, attrs')];

      assert Valid() by {
        mk_data_at(ino);
        assert is_dir(ino);
        assert is_of_type(ino, fs.types[ino].ty) by { reveal is_of_type(); }
        ValidData_change_one(ino);
        assert ValidRoot() by { reveal ValidRoot(); }
      }

      r := Ok(());
      return;
    }

    // public
    method SETATTR(txn: Txn, ino: uint64, attrs: Sattr3)
      returns (r:Result<()>, ghost attrs': Inode.Attrs)
      modifies Repr
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> ino !in data
      ensures r.ErrIsDir? ==> ino_ok(ino) && old(is_dir(ino))
      ensures r.Ok? ==>
      && old(ino in data)
      && has_set_attrs(old(data[ino].attrs), attrs', attrs)
      && (old(is_file(ino)) ==> (var d0 := old(data[ino]);
        var sz := if attrs.size.Some? then attrs.size.x as nat else |d0.data|;
        var d' := ByteFs.ByteFilesys.setSize_with_zeros(d0.data, sz);
        data == old(data[ino := ByteFile(d', attrs')])))
      && (old(is_dir(ino)) ==> (var d0 := old(data[ino]);
        data == old(data[ino := DirFile(d0.dir, attrs')])))
    {
      var ino :- checkInoBounds(ino);
      if attrs.size.Some? && attrs.size.x > Inode.MAX_SZ_u64 {
        r := Err(FBig);
        return;
      }
      var ok, i := fs.startInode(txn, ino);
      if !ok {
        r := Err(BadHandle);
        assert is_invalid(ino) by { reveal is_of_type(); }
        return;
      }

      if i.ty().FileType? {
        // we handle files inline here - they are quite different from other
        // file types because SETATTR can truncate the file
        assert old(is_file(ino)) by { reveal is_of_type(); }
        var sz: uint64 := attrs.size.get_default(i.sz);
        assert dirents == old(dirents);
        ghost var attrs0 := data[ino].attrs;
        ghost var d0: seq<byte> := old(fs.data[ino]);
        assert Valid_file_at(ino, fs.data, fs.types) by {
          get_data_at(ino);
        }

        fs.inode_metadata(ino, i);
        assert this !in fs.Repr;

        var attrs'_val := SetattrAttributes(attrs, i.attrs);
        attrs' := attrs'_val;
        fs.setAttrs(ino, i, attrs'_val);
        var setsize_r := fs.setSize(txn, ino, i, sz);
        if setsize_r.SetSizeNotZero? {
          r := Err(JukeBox(sz));
          return;
        }
        if setsize_r.SetSizeNoSpc? {
          r := Err(NoSpc);
          return;
        }
        fs.finishInode(txn, ino, i);

        ghost var d' := ByteFs.ByteFilesys.setSize_with_zeros(d0, sz as nat);
        data := data[ino := ByteFile(d', attrs')];

        assert Valid() by {
          file_change_with_attrs_valid(ino, d', attrs');
        }

        r := Ok(());
        return;
      }

      if i.ty().DirType? {
        assert old(is_dir(ino)) by { reveal is_of_type(); }
        r, attrs' := SETATTRdir(txn, ino, i, attrs);
        return;
      }

      // no more file types (for now...)
      assert false;
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
      ensures dirents == old(dirents)
    {
      var ok, i := fs.startInode(txn, ino);
      if !ok {
        assert is_invalid(ino) by { reveal is_of_type(); }
        return Err(BadHandle);
      }
      if i.ty().DirType? {
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
      requires data == old(data[ino := ByteFile(d', data[ino].attrs)])
      ensures Valid()
    {
      assert old(this).is_of_type(ino, old(fs.types)[ino].ty) by {
        reveal is_of_type();
      }
      assert old(Valid_file_at(ino, fs.data, fs.types)) by {
        reveal Valid_data_at();
        // BUG: surely this shouldn't be necessary
        assert old(Valid_data_at(ino, fs.data, fs.types));
      }
      assert is_of_type(ino, fs.types[ino].ty) by {
        reveal is_of_type();
      }
      mk_data_at(ino);
      ValidData_change_one(ino);
      assert ValidRoot() by { reveal ValidRoot(); }
    }

    twostate lemma file_change_with_attrs_valid(ino: Ino, d': seq<byte>, new attrs': Inode.Attrs)
      requires old(Valid()) && fs.Valid()
      requires old(is_file(ino))
      requires attrs'.ty == old(fs.types[ino].ty)
      requires fs.data == old(fs.data[ino := d'])
      requires fs.types == old(fs.types[ino := attrs'])
      requires dirents == old(dirents)
      requires data == old(data[ino := ByteFile(d', attrs')])
      ensures Valid()
    {
      assert old(this).is_of_type(ino, old(fs.types)[ino].ty) by {
        reveal is_of_type();
      }
      assert old(Valid_file_at(ino, fs.data, fs.types)) by {
        reveal Valid_data_at();
        // BUG: surely this shouldn't be necessary
        assert old(Valid_data_at(ino, fs.data, fs.types));
      }
      assert is_of_type(ino, fs.types[ino].ty) by {
        reveal is_of_type();
      }
      mk_data_at(ino);
      ValidData_change_one(ino);
      assert ValidRoot() by { reveal ValidRoot(); }
    }

    static method ModifyAttrs(attrs: Inode.Attrs) returns (attrs': Inode.Attrs)
      ensures has_modify_attrs(attrs, attrs')
    {
      var mtime := serverTime();
      return attrs.(mtime := mtime);
    }

    static method RootAttrs(uid: uint32, gid: uint32) returns (attrs: Inode.Attrs)
      ensures has_root_attrs(attrs, uid, gid)
    {
      var mtime := serverTime();
      attrs := Inode.Attrs.zero_dir;
      attrs := attrs.(mtime := mtime).(uid := uid).(gid := gid).(mode := 511);
      // we prove here that 511 is the decimal value for the octal 0777
      return;
    }

    // public
    method {:timeLimitMultiplier 3} WRITE(txn: Txn, ino: uint64, off: uint64, bs: Bytes)
      returns (r: Result<Fattr3>)
      modifies Repr, bs
      requires Valid()
      requires fs.has_jrnl(txn)
      requires |bs.data| <= WT_MAX as nat
      // nothing to say in error case (need to abort)
      ensures r.Ok? ==> Valid()
      ensures r.ErrBadHandle? ==> ino !in old(data)
      ensures (r.Err? && r.err.Inval?) ==> ino in old(data) && old(data[ino].DirFile?)
      ensures r.Ok? ==>
      var fattr := r.v;
      var attrs := fattr.attrs;
      && ino in old(data) && old(data[ino].ByteFile?)
      && has_modify_attrs(old(data[ino].attrs), attrs)
      && (var file := old(
      var d0 := data[ino];
      var d' := ByteFs.write_data_holes(d0.data, off as nat, bs.data);
      ByteFile(d', attrs));
      && is_file_attrs(file, fattr)
      && data == old(data[ino := file]))
    {
      var ino :- checkInoBounds(ino);
      var i_r := openFile(txn, ino);
      var i :- i_r.IsDirToInval();
      assert dirents == old(dirents);
      invert_file(ino);
      assert ValidIno(ino, i);
      ghost var attrs0 := old(data[ino].attrs);
      ghost var d0: seq<byte> := old(fs.data[ino]);
      assert d0 == old(data[ino].data) && i.attrs == attrs0 by {
        fs.inode_metadata(ino, i);
        get_data_at(ino);
      }

      // update mtime
      //
      // we do this first because it's annoying to prove that the attributes
      // aren't affected by the setSize and write later
      fs.inode_metadata(ino, i);
      var new_attrs := ModifyAttrs(i.attrs);
      fs.setAttrs(ino, i, new_attrs);

      if i.sz + bs.Len() > Inode.MAX_SZ_u64 ||
        sum_overflows(off, bs.Len()) ||
        off + bs.Len() > Inode.MAX_SZ_u64 {
        return Err(FBig);
      }
      var createHole := off > i.sz;
      if createHole {
        fs.inode_metadata(ino, i);
        var setsize_r := fs.setSize(txn, ino, i, off);
        if setsize_r.SetSizeNotZero? {
          return Err(JukeBox(off));
        }
        if setsize_r.SetSizeNoSpc? {
          return Err(NoSpc);
        }
        assert |fs.data[ino]| == off as nat;
      }
      fs.inode_metadata(ino, i);

      assert this !in fs.Repr;
      var ok;
      ok := fs.write(txn, ino, i, off, bs);
      if !ok {
        return Err(NoSpc);
      }
      if createHole {
        assert fs.data[ino] ==
          old(fs.data[ino]) +
          C.repeat(0 as byte, off as nat - old(|fs.data[ino]|)) +
          old(bs.data);
      }
      var sz := i.sz;
      assert sz as nat == |fs.data[ino]| by {
        fs.inode_metadata(ino, i);
      }

      fs.finishInode(txn, ino, i);

      ghost var f' := ByteFile(fs.data[ino], new_attrs);
      data := data[ino := f'];

      assert Valid() by {
        file_change_with_attrs_valid(ino, f'.data, new_attrs);
      }
      var fattr := Fattr3(NFS3REG, sz, new_attrs);
      return Ok(fattr);
    }

    // public
    method READ(txn: Txn, ino: uint64, off: uint64, len: uint64)
      returns (r: Result<ReadResult>)
      modifies fs.fs.fs.fs
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==> ino !in data
      ensures r.ErrInval? ==> ino in data && data[ino].DirFile?
      ensures r.Ok? ==>
      (var bs := r.v.data;
       var eof := r.v.eof;
      && ino in data && data[ino].ByteFile?
      && is_read_data(data[ino].data, off as nat, len as nat, bs.data, eof)
      )
    {
      if len > 32*4096 {
        // we should really return a short read
        var bs := NewBytes(0);
        return Err(ServerFault);
      }
      var ino :- checkInoBounds(ino);
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

    // public
    method {:timeLimitMultiplier 2} MKDIR(txn: Txn,
      d_ino: uint64, name: Bytes, sattr: Sattr3)
      returns (r: Result<CreateResult>)
      modifies Repr
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      requires name.Valid()
      ensures (r.Err? && r.err.Exist?) ==>
      && ino_ok(d_ino)
      && old(is_dir(d_ino))
      && is_pathc(name.data)
      && name.data in old(data[d_ino].dir)
      ensures r.Ok? ==>
      (var ino := r.v.ino;
      var attrs' := r.v.attrs.attrs;
      && ino_ok(d_ino)
      && old(is_dir(d_ino))
      && old(is_invalid(ino))
      && old(valid_name(name.data))
      && has_before_attrs(old(data[d_ino].attrs), r.v.dir_before)
      && has_mkdir_attrs(attrs', sattr)
      && data == old(
        var d0 := data[d_ino];
        var d' := DirFile(d0.dir[name.data := ino], d0.attrs);
        data[ino := DirFile(map[], attrs')][d_ino := d'])
      )
    {
      var _ :- validatePath(name);
      var d_ino :- checkInoBounds(d_ino);
      var attrs'_val := MkdirAttributes(sattr);
      var attrs' := attrs'_val;
      var ok, ino := allocDir(txn, attrs'_val);
      if !ok {
        r := Err(NoSpc);
        return;
      }
      // we allocate before reading d_ino because readDirents keeps the
      // directory open; if the caller guesses the newly-allocated directory, we
      // should fail
      if d_ino == ino {
        r := Err(Inval);
        return;
      }

      var dents :- readDirents(txn, d_ino);
      assert dents.Repr() !! Repr;
      assert name !in Repr;
      assert ino != d_ino;
      var before_sz := dents.getSizeBytes();
      var before_attrs := dents.getAttrs();
      var dir_before := BeforeAttr(before_sz, before_attrs.mtime);
      //assert is_dir(d_ino);
      get_data_at(d_ino);
      var name_opt := dents.findName(txn, name);
      if name_opt.Some? {
        dents.val.findName_found(name.data);
        r := Err(Exist);
        return;
      }
      dents.val.findName_not_found(name.data);
      var dattrs := dents.getAttrs();
      var dsz := dents.getSizeBytes();

      var e' := MemDirEnt(name, ino);
      assert name.data == old(name.data);
      assert dents.Valid() && e'.Valid() && e'.used();
      ok := linkInode(txn, d_ino, dents, e');
      if !ok {
        r := Err(NoSpc);
        return;
      }
      var fattr := Fattr3(NFS3DIR, 0, attrs');
      // this is the directory we are creating in, not the new directory
      var dattr3 := Fattr3(NFS3DIR, dsz, dattrs);
      r := Ok(CreateResult(ino, fattr, dir_before, dattr3));
      return;
    }

    // public
    method LOOKUP(txn: Txn, d_ino: uint64, name: Bytes)
      // note that LOOKUP returns directory attributes even on failure (in most
      // cases, at least)
      returns (r:Result<InoResult>, dattr3: Option<Fattr3>)
      modifies fs.fs.fs.fs
      requires Valid() ensures Valid()
      requires fs.has_jrnl(txn)
      requires name.Valid()
      ensures r.ErrBadHandle? ==> d_ino !in data
      ensures r.ErrNoent? ==> ino_ok(d_ino) && is_dir(d_ino) &&
      (name.data !in data[d_ino].dir
      || (name.data in data[d_ino].dir && data[d_ino].dir[name.data] !in data))
      ensures r.Err? && dattr3.Some? ==>
              old(d_ino in data) && is_file_attrs(old(data[d_ino]), dattr3.x)
      ensures r.Ok? ==>
      (var ino := r.v.ino;
       var attrs := r.v.attrs;
      && is_pathc(name.data)
      && ino_ok(d_ino)
      && is_dir(d_ino)
      && name.data in data[d_ino].dir
      && data[d_ino].dir[name.data] == ino && ino != 0
      && ino in data
      && is_file_attrs(data[ino], attrs)
      && dattr3.Some? && is_file_attrs(data[d_ino], dattr3.x)
      )
    {
      dattr3 := None;
      var path_ok := Pathc?(name);
      if !path_ok {
        return Err(NameTooLong), None;
      }

      var d_ino :- checkInoBounds(d_ino);
      var dents :- readDirents(txn, d_ino);
      assert dents.dir() == data[d_ino].dir by {
        get_data_at(d_ino);
      }
      assert name != dents.file.bs by {
        assert dents.file.bs in dents.Repr();
      }
      var attr3 := dirFattr3(d_ino, dents);
      dattr3 := Some(attr3);
      var name_opt := dents.findName(txn, name);
      dents.finishReadonly();
      if name_opt.None? {
        return Err(Noent), dattr3;
      }
      var ino: Ino := name_opt.x.1;
      dents.val.findName_found(name.data);
      var ok, i := fs.startInode(txn, ino);
      if !ok {
        // TODO: probably shouldn't happen, inodes should be valid, but this
        // isn't part of the invariant
        assert is_invalid(ino) by { reveal is_of_type(); }
        return Err(Noent), dattr3;
      }
      assert ino in data by {
        reveal is_of_type();
      }
      var attr := inodeFattr3(ino, i);
      fs.finishInodeReadonly(ino, i);

      return Ok(InoResult(ino, attr)), dattr3;
    }

    // this is a low-level function that deletes an inode (currently restricted
    // to files) from the tree
    method removeInode(txn: Txn, ino: Ino)
      // returns the size of the inode (as a hint for freeing space)
      returns (r: Result<uint64>)
      modifies Repr
      requires Valid() ensures Valid()
      requires fs.has_jrnl(txn)
      ensures r.ErrBadHandle? ==>
      && is_invalid(ino)
      && data == old(data) == old(map_delete(data, ino))
      && dirents == old(dirents)
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
      if i.ty() == Inode.DirType {
        assert is_dir(ino) by { reveal is_of_type(); }
        fs.finishInodeReadonly(ino, i);
        return Err(IsDir);
      }
      assert is_file(ino) by { reveal is_of_type(); }
      fs.freeInode(txn, ino, i);
      var sz := i.sz;
      //map_delete_not_in(data, ino);
      data := map_delete(data, ino);

      assert dirents == old(dirents);
      mk_invalid_type(ino);
      mk_data_at(ino);
      ValidData_change_one(ino);
      assert ValidRoot() by { reveal ValidRoot(); }
      return Ok(sz);
    }

    method unlinkInodeAt(txn: Txn, d_ino: Ino, dents: MemDirents, name: Bytes,
      // i and ino are the result of a succesfull findName call
      i: uint64, ghost ino: Ino)
      returns (r: Result<Fattr3>)
      modifies Repr, dents.Repr(), dents.file.i.Repr
      requires fs.has_jrnl(txn)
      requires is_pathc(name.data)
      requires name != dents.file.bs
      requires name !in dents.file.i.Repr
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
      && is_dir(d_ino)
      && is_file_attrs(data[d_ino], r.v)
      && data ==
        (var d0 := old(data[d_ino]);
        var d' := map_delete(d0.dir, old(name.data));
        old(data)[d_ino := DirFile(d', d0.attrs)])
    {
      ghost var path := name.data;
      invert_dir(d_ino);
      ghost var attrs0 := old(data[d_ino].attrs);
      assert dents.dir() == data[d_ino].dir &&
             fs.types[d_ino] == attrs0 by {
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
      var attrs := dents.getAttrs();
      var d_sz := dents.getSizeBytes();
      var attr3 := Fattr3(NFS3DIR, d_sz, attrs);
      dents.finish(txn);

      dirents := dirents[d_ino := dents.val];
      ghost var d': Directory := dents.val.dir;
      assert d' == map_delete(d0, path);
      data := data[d_ino := DirFile(d', attrs0)];

      assert is_dir(d_ino);
      assert is_of_type(d_ino, fs.types[d_ino].ty) by { reveal is_of_type(); }
      // not necessary but helps the proof a bit
      assert Valid_dir_at(d_ino, fs.types) by {
        assert data[d_ino].attrs == fs.types[d_ino] == attrs0;
      }
      mk_data_at(d_ino);
      ValidData_change_one(d_ino);
      assert Valid() by {
        assert ValidRoot() by { reveal ValidRoot(); }
      }
      reveal ino_ok;
      return Ok(attr3);
    }

    method unlinkInode(txn: Txn, d_ino: Ino, dents: MemDirents, name: Bytes)
      returns (r: Result<(Ino, Fattr3)>)
      modifies Repr, dents.Repr(), dents.file.i.Repr
      requires fs.has_jrnl(txn)
      requires is_pathc(name.data)
      requires name != dents.file.bs
      requires name !in dents.file.i.Repr
      requires ValidDirents(dents, d_ino) ensures r.Ok? ==> Valid()
      ensures r.ErrNoent? ==> name.data !in old(data[d_ino].dir)
      ensures r.Err? ==> r.err.Noent? || r.err.NoSpc?
      ensures r.Ok? ==>
      && old(name.data in data[d_ino].dir)
      && r.v.0 == old(data[d_ino].dir[name.data])
      && is_dir(d_ino)
      && is_file_attrs(data[d_ino], r.v.1)
      && data ==
        (var d0 := old(data[d_ino]);
        var d' := map_delete(d0.dir, old(name.data));
        old(data)[d_ino := DirFile(d', d0.attrs)])
    {
      ghost var path := name.data;
      assert dents.Repr() !! Repr;

      assert dents.dir() == data[d_ino].dir by {
        get_data_at(d_ino);
      }
      var name_opt := dents.findName(txn, name);
      if name_opt.None? {
        return Err(Noent);
      }

      var i := name_opt.x.0;
      var ino := name_opt.x.1;

      var attr3 :- unlinkInodeAt(txn, d_ino, dents, name, i, ino);
      return Ok((ino, attr3));
    }

    method unlink(txn: Txn, d_ino: Ino, name: Bytes)
      returns (r: Result<(Ino, BeforeAttr, Fattr3)>)
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
      && is_dir(d_ino)
      && name.data in old(data[d_ino].dir)
      && r.v.0 == old(data[d_ino].dir[name.data])
      && has_before_attrs(old(data[d_ino].attrs), r.v.1)
      && is_file_attrs(data[d_ino], r.v.2)
      && data ==
        (var d0 := old(data[d_ino]);
        var d' := map_delete(d0.dir, old(name.data));
        old(data)[d_ino := DirFile(d', d0.attrs)])
    {
      ghost var path := name.data;
      var dents :- readDirents(txn, d_ino);
      var sz := dents.getSizeBytes();
      var dir_attr := dents.getAttrs();
      var dir_before := BeforeAttr(sz, dir_attr.mtime);
      assert has_before_attrs(old(data[d_ino].attrs), dir_before) by {
        get_data_at(d_ino);
      }
      assert old(is_dir(d_ino));
      assert fresh(dents.file.bs) by {
        assert dents.file.bs in dents.Repr();
      }
      var unlink_r := unlinkInode(txn, d_ino, dents, name);
      if unlink_r.Err? {
        return Err(unlink_r.err);
      }
      return Ok((unlink_r.v.0, dir_before, unlink_r.v.1));
    }

    // public
    method REMOVE(txn: Txn, d_ino: uint64, name: Bytes)
      // returns a hint for what free space to erase, and the dir_wcc
      returns (r: Result<RemoveResult>)
      modifies Repr
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      requires name.Valid()
      ensures r.ErrBadHandle? ==> d_ino !in old(data)
      ensures r.ErrNoent? ==>
      && ino_ok(d_ino)
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
      && ino_ok(d_ino)
      && old(is_dir(d_ino))
      && is_dir(d_ino)
      && is_pathc(name.data)
      && name.data in old(data[d_ino].dir)
      && has_before_attrs(old(data[d_ino].attrs), r.v.dir_before)
      && is_file_attrs(data[d_ino], r.v.d_attrs)
      && data ==
        (var d0 := old(data[d_ino]);
        var d' := map_delete(d0.dir, old(name.data));
        map_delete(old(data)[d_ino := DirFile(d', d0.attrs)], d0.dir[old(name.data)]))
    {
      var path_ok := Pathc?(name);
      if !path_ok {
        return Err(NameTooLong);
      }
      var d_ino :- checkInoBounds(d_ino);
      var ino_attrs :- this.unlink(txn, d_ino, name);
      var ino := ino_attrs.0;
      var dir_before := ino_attrs.1;
      var attr3 := ino_attrs.2;

      var remove_r := removeInode(txn, ino);

      if remove_r.ErrBadHandle? {
        assert ino != d_ino;
        return Ok(RemoveResult(ino, 0, dir_before, attr3));
      }

      if remove_r.Err? {
        assert remove_r.ErrIsDir?;
        return Err(IsDir);
      }

      var sz_hint := remove_r.v;
      return Ok(RemoveResult(ino, sz_hint, dir_before, attr3));
    }

    method removeEmptyDir(txn: Txn, ino: Ino)
      returns (r: Result<()>)
      modifies Repr
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      requires ino != rootIno
      ensures r.Err? ==> r.err.NotEmpty? || r.err.BadHandle? || r.err.NotDir?
      ensures r.ErrBadHandle? ==>
        old(is_invalid(ino))
      ensures r.ErrNotDir? ==>
        && old(is_file(ino))
      ensures r.Err? && r.err.NotEmpty? ==>
        && old(is_dir(ino))
        && old(data)[ino].dir != map[]
      ensures r.Ok? ==>
        && old(is_dir(ino))
        && old(data)[ino].dir == map[]
        && data == old(map_delete(data, ino))
        && dirents == old(map_delete(dirents, ino))
    {
      var ok, i := fs.startInode(txn, ino);
      if !ok {
          assert is_invalid(ino) by { reveal is_of_type(); }
          return Err(BadHandle);
      }
      if i.ty().FileType? {
        fs.finishInodeReadonly(ino, i);
        assert is_file(ino) by { reveal is_of_type(); }
        return Err(NotDir);
      }

      assert is_dir(ino) by { reveal is_of_type(); }
      var dents := readDirentsInode(txn, ino, i);
      var is_empty := dents.isEmpty(txn);
      if !is_empty {
        get_data_at(ino);
        assert data[ino].dir != map[];
        return Err(NotEmpty);
      }
      assert data[ino].dir == map[] by {
        get_data_at(ino);
      }

      fs.freeInode(txn, ino, i);
      data := map_delete(data, ino);
      dirents := map_delete(dirents, ino);

      mk_invalid_type(ino);
      mk_data_at(ino);
      ValidData_change_one(ino);
      assert ValidRoot() by { reveal ValidRoot(); }
      return Ok(());
    }

    // public
    method {:timeLimitMultiplier 2} RMDIR(txn: Txn, d_ino: uint64, name: Bytes)
      returns (r: Result<()>)
      modifies Repr
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      requires name.Valid()
      ensures r.ErrBadHandle? ==> d_ino !in old(data)
      ensures r.ErrNoent? ==>
      && ino_ok(d_ino)
      && old(is_dir(d_ino))
      && is_pathc(name.data)
      && name.data !in old(data[d_ino].dir)
      ensures r.ErrNotDir? ==>
      && is_pathc(name.data)
      && ino_ok(d_ino)
      && (old(is_file(d_ino))
        || (&& old(d_ino in data && data[d_ino].DirFile?)
          && old(name.data) in old(data[d_ino].dir)
          && (var ino := old(data[d_ino].dir[name.data]);
            && ino in old(data)
            && old(data[ino].ByteFile?))))
      ensures r.Ok? ==>
      && ino_ok(d_ino)
      && old(is_dir(d_ino))
      && is_pathc(name.data)
      && name.data in old(data[d_ino].dir)
      && var d0 := old(data[d_ino]);
        var n := old(name.data);
        var d' := map_delete(d0.dir, n);
        && d0.dir[n] in old(data)
        && old(data)[d0.dir[n]].DirFile?
        && old(data)[d0.dir[n]].dir == map[]
        && data ==
          map_delete(old(data)[d_ino := DirFile(d', d0.attrs)], d0.dir[n])
    {
      var path_ok := Pathc?(name);
      if !path_ok {
        return Err(NameTooLong);
      }
      var d_ino :- checkInoBounds(d_ino);
      var ino_attr :- this.unlink(txn, d_ino, name);
      var ino := ino_attr.0;
      if ino == rootIno || ino == d_ino {
        return Err(Inval);
      }
      var remove := removeEmptyDir(txn, ino);
      if remove.Err? && remove.err.BadHandle? {
        // the directory somehow held an invalid entry; this could probably
        // legitimately return ERR_NOENT, but our spec doesn't have a case for
        // this
        return Err(ServerFault);
      }
      if remove.Err? {
        return Err(remove.err);
      }

      return Ok(());
    }

    // public
    method READDIR(txn: Txn, d_ino: uint64)
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
      var d_ino :- checkInoBounds(d_ino);
      var dents :- readDirents(txn, d_ino);
      assert dents.dir() == data[d_ino].dir by {
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
      returns (r: Result<MemDirents>, removed: Option<Ino>)
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
      && old(is_dir(d_ino))
      && is_dir(d_ino)
      && (name.data in old(data[d_ino].dir) ==>
         var d0 := old(data[d_ino]);
         var d' := map_delete(d0.dir, old(name.data));
         && removed == Some(d0.dir[old(name.data)])
         && data == old(data)[d_ino := DirFile(d', d0.attrs)]
         )
      && (name.data !in old(data[d_ino].dir) ==>
         && removed == None
         && data == old(data)
         )
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
        get_data_at(d_ino);
        assert name.data !in old(data[d_ino]).dir;
        return Ok(dents), None;
      }
      var i := name_opt.x.0;
      var dst_ino := name_opt.x.1;
      assert name.data in data[d_ino].dir && data[d_ino].dir[name.data] == dst_ino by {
        get_data_at(d_ino);
      }
      var _ :- unlinkInodeAt(txn, d_ino, dents, name, i, dst_ino);

      // unlinkInodeAt closes dents, so we need to re-open (the proof of
      // unlinkInodeAt is extremely hairy and we wouldn't want to re-do it here)
      dents :- assert readDirents(txn, d_ino);

      assert fresh(dents.file.Repr()) by {
        assert dents.file.Repr() <= dents.Repr();
      }

      // re-confirm that name was removed; proving this from unlinkInodeAt's
      // postcondition is tricky (or it might not be strong enough)
      name_opt := dents.findName(txn, name);
      if name_opt.Some? {
        return Err(ServerFault), None;
      }
      return Ok(dents), Some(dst_ino);
    }


    // rename and overwrite the destination unconditionally
    method {:timeLimitMultiplier 2} renameOverwrite(txn: Txn,
      src_d_ino: Ino, src_name: Bytes, dst_d_ino: Ino, dst_name: Bytes)
      returns (r: Result<(Ino, Option<Ino>)>)
      modifies Repr
      requires is_pathc(src_name.data) && is_pathc(dst_name.data)
      requires Valid() ensures r.Ok? ==> Valid()
      ensures r.Ok? ==>
      var args := RenameArgs(src_d_ino, old(src_name.data), dst_d_ino, old(dst_name.data));
      && rename_overwrite_ok(args, old(data))
      && data == rename_overwrite_spec(args, old(data))
      && var src_ino := r.v.0;
        var m_dst_ino := r.v.1;
      && old(data)[args.src].dir[args.src_name] == src_ino
      && src_ino != src_d_ino && src_ino != dst_d_ino
      && (m_dst_ino.None? ==> args.dst_name !in old(data)[args.dst].dir || args.trivial())
      && (m_dst_ino.Some? ==>
          var dst_ino := m_dst_ino.x;
           && dst_ino != src_ino
           && dst_ino != dst_d_ino
           && args.dst_name in old(data)[args.dst].dir
           && old(data)[args.dst].dir[args.dst_name] == dst_ino)
      requires fs.has_jrnl(txn)
    {
      ghost var args := RenameArgs(src_d_ino, src_name.data,
        dst_d_ino, dst_name.data);
      var ino_attr :- unlink(txn, src_d_ino, src_name);
      var ino := ino_attr.0;
      if ino == 0 {
        return Err(Inval);
      }
      // circular directory structure (src_d_ino/src_name points back to src_d_ino)
      if ino == src_d_ino { return Err(ServerFault); }
      // would create a circular link from destination directory to itself
      if ino == dst_d_ino { return Err(Inval); }
      assert is_dir(src_d_ino);
      var dst, removed :- readWithNameFree(txn, dst_d_ino, dst_name);
      if removed.Some? && (removed.x == ino || removed.x == dst_d_ino) {
        return Err(ServerFault);
      }
      assert dst_name != dst.file.bs by {
        assert dst.file.bs in dst.Repr();
      }
      var e' := MemDirEnt(dst_name, ino);
      var ok := linkInode(txn, dst_d_ino, dst, e');
      if !ok {
        return Err(NoSpc);
      }
      assert Valid();
      ghost var src_f := old(data[src_d_ino].dir[src_name.data]);
      ghost var src_name := args.src_name;
      ghost var dst_name := args.dst_name;
      assert rename_overwrite_ok(args, old(data));
      assert data == rename_overwrite_spec(args, old(data)) by {
        if src_d_ino == dst_d_ino {
          assert data[dst_d_ino].dir == old(map_delete(data[src_d_ino].dir, src_name)[dst_name := src_f]);
          rename_overwrite_spec_same_dir_ok(args, old(data));
        } else if removed.Some? {
          assert data[src_d_ino].dir == old(map_delete(data[src_d_ino].dir, src_name));
          assert data[dst_d_ino].dir == old(data[dst_d_ino].dir[dst_name := src_f]);
          assert data == rename_overwrite_spec(args, old(data));
        }
      }
      return Ok((ino, removed));
    }

    method {:timeLimitMultiplier 2} renameWithCleanup(txn: Txn,
      locks: LockHint,
      src_d_ino: Ino, src_name: Bytes, dst_d_ino: Ino, dst_name: Bytes)
      returns (r: Result<()>)
      modifies Repr
      requires is_pathc(src_name.data) && is_pathc(dst_name.data)
      requires Valid() ensures r.Ok? ==> Valid()
      ensures r.Ok? ==>
      var args := RenameArgs(src_d_ino, old(src_name.data), dst_d_ino, old(dst_name.data));
      && rename_ok(args, old(data))
      && data == rename_spec(args, old(data))
      requires fs.has_jrnl(txn)
    {
      var trivial := false;
      if src_d_ino == dst_d_ino {
        assert src_name.Valid() && dst_name.Valid() by {
          reveal is_pathc();
        }
        var eq := ByteHelpers.Equal(src_name, dst_name);
        if eq {
          trivial := true;
        }
      }
      var src_dst :- renameOverwrite(txn, src_d_ino, src_name, dst_d_ino, dst_name);
      if trivial {
        return Ok(());
      }
      ghost var args := RenameArgs(src_d_ino, old(src_name.data), dst_d_ino, old(dst_name.data));
      assert !args.trivial();
      var src := src_dst.0;
      var removed := src_dst.1;
      if removed.None? {
        return Ok(());
      }
      var dst_ino := removed.x;
      if !LockOrder.safe_lock(locks, src) {
        return Err(LockOrderViolated(LockOrder.insert_lock_hint(locks, src)));
      }
      var locks := LockOrder.insert_lock_hint(locks, src);
      var t := fs.getInodeType(txn, src);
      if t.InvalidType? {
        // we had an invalid file in a directory, something is wrong
        return Err(ServerFault);
      }
      if !LockOrder.safe_lock(locks, dst_ino) {
        return Err(LockOrderViolated(LockOrder.insert_lock_hint(locks, dst_ino)));
      }
      if t.FileType? {
        assert is_file(src) by { reveal is_of_type(); }
        var _ :- removeInode(txn, dst_ino);
        // should have right errors?
        return Ok(());
      } else {
        assert t.DirType?;
        assert is_dir(src) by { reveal is_of_type(); }
        if removed.x == rootIno {
          // root should not be in another directory
          return Err(ServerFault);
        }
        ghost var data_delete: Fs := old(data)[args.src := old(data)[args.src].delete(args.src_name)];
        ghost var data_pre_cleanup: Fs := data;
        var _ :- removeEmptyDir(txn, dst_ino);
        assert data_delete[dst_ino] == data_pre_cleanup[dst_ino];
        return Ok(());
      }
    }

    // public
    method RENAME(txn: Txn, locks: LockHint,
      src_d_ino: uint64, src_name: Bytes, dst_d_ino: uint64, dst_name: Bytes)
      returns (r: Result<()>)
      modifies Repr
      requires src_name.Valid() && dst_name.Valid()
      requires Valid() ensures r.Ok? ==> Valid()
      requires fs.has_jrnl(txn)
      ensures r.Ok? ==>
        && ino_ok(src_d_ino)
        && ino_ok(dst_d_ino)
        // we validate the destination name fully to avoid creating an invalid path
        && valid_name(old(dst_name.data))
        && var args := RenameArgs(src_d_ino, old(src_name.data),
                                dst_d_ino, old(dst_name.data));
          && rename_ok(args, old(data))
          && data == rename_spec(args, old(data))
    {
      var src_name_ok := Pathc?(src_name);
      if !src_name_ok {
        return Err(NameTooLong);
      }
      var _ :- validatePath(dst_name);
      var src_d_ino :- checkInoBounds(src_d_ino);
      var dst_d_ino :- checkInoBounds(dst_d_ino);

      // to avoid deadlock, ensure that directories are locked
      var locks := LockOrder.insert_lock_hints(locks, [src_d_ino, dst_d_ino]);

      {
        fs.reveal_valids();
        fs.fs.fs.fs.lockInodes(txn, locks);
      }
      var _ :- renameWithCleanup(txn, locks, src_d_ino, src_name, dst_d_ino, dst_name);
      return Ok(());
    }

    // public
    method FSSTAT() returns (r: Fsstat3)
      requires Valid()
    {
      fs.reveal_valids();
      var tbytes := fs.fs.fs.fs.TotalBytes();
      var fbytes := fs.fs.fs.fs.FreeBytes();
      var tfiles := fs.TotalFiles();
      var ffiles := fs.FreeFiles();
      r := Fsstat3.zero;
      r := r.(tbytes := tbytes).(fbytes := fbytes);
      r := r.(tfiles := tfiles).(ffiles := ffiles);
      return;
    }

    // public
    //
    // Returns Ok(true) if this inode now has all its free space zeroed. Caller
    // should call in a loop until this method returns true.
    method ZeroFreeSpace(txn: Txn, ino: uint64, sz_hint: uint64)
      returns (r: Result<bool>)
      modifies Repr
      requires fs.has_jrnl(txn)
      requires Valid() ensures Valid()
      ensures r.Ok? // only return a Result to use runTxn in Go
      ensures data == old(data)
    {
      var ok := is_ino_ok(ino);
      if !ok {
        // not a valid inode, consider it done
        return Ok(true);
      }
      var done := fs.zeroFreeSpace(txn, ino, sz_hint);
      return Ok(done);
    }
  }
}
