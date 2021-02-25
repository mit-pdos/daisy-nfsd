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
    | NoError
    | DoesNotExist
    | NotADir
    | IsADir
  {
    predicate method IsError()
    {
      !this.NoError?
    }
  }

  datatype StatRes = StatRes(is_dir: bool, size: uint64)

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

    const Repr: set<object> := {this} + fs.Repr + ialloc.Repr

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

    static method createRootDir(fs: ByteFilesys<()>, txn: Txn) returns (ok: bool)
      modifies fs.Repr
      requires fs.Valid() ensures ok ==> fs.Valid()
      requires fs.fs.has_jrnl(txn)
      requires forall ino:Ino :: fs.data()[ino] == []
      ensures ok ==>
      && fs.data() == old(fs.data()[rootIno := Dirents.zero.enc()])
      && fs.inode_types() == old(fs.inode_types()[rootIno := Inode.DirType])
    {
      var ino := rootIno;

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
      var ok := createRootDir(fs_, txn);
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

    method startInode(txn: Txn, ino: Ino)
      returns (i: Inode.Inode)
      modifies fs.fs.fs
      requires fs.fs.has_jrnl(txn)
      requires Valid()
      ensures ValidIno(ino, i) && i.meta.ty == fs.inode_types()[ino]
      ensures fs.fs.fs.cur_inode == Some( (ino, i) )
      ensures data == old(data)
      ensures dirents == old(dirents)
      ensures fs.types_unchanged()
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
      returns (err: Error, dents: Dirents)
      modifies fs.fs.fs
      requires Valid() ensures Valid()
      requires fs.fs.has_jrnl(txn)
      ensures err.NoError? ==> is_dir(d_ino) && dents == dirents[d_ino]
      ensures err.DoesNotExist? ==> is_invalid(d_ino)
      ensures err.NotADir? ==> is_file(d_ino)
      ensures !err.IsADir?
    {
      var i := startInode(txn, d_ino);
      if !i.meta.ty.DirType? {
        fs.finishInodeReadonly(d_ino, i);
        assert ValidData() by {
          reveal ValidFiles();
        }
        if i.meta.ty.InvalidType? {
          assert is_invalid(d_ino) by { reveal is_of_type(); }
          err := DoesNotExist;
          return;
        }
        // is a file
        assert is_file(d_ino) by { reveal is_of_type(); }
        err := NotADir;
        return;
      }
      assert is_dir(d_ino) by { reveal is_of_type(); }
      err := NoError;
      dents := readDirentsInode(txn, d_ino, i);
      fs.finishInodeReadonly(d_ino, i);
      assert ValidData() by {
        reveal ValidFiles();
      }
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

    method writeDirents(txn: Txn, d_ino: Ino, dents: Dirents)
      returns (ok:bool)
      modifies Repr
      requires fs.fs.has_jrnl(txn)
      requires Valid() ensures Valid()
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
        assert ValidData() by {
          reveal ValidFiles();
          reveal ValidDirs();
        }
        assert ValidRoot() by { reveal ValidRoot(); }
        assert ValidTypes() by { reveal is_of_type(); }
        return;
      }

      dirents := dirents[d_ino := dents];
      data := data[d_ino := DirFile(dents.dir)];

      assert is_dir(d_ino);
      assert ValidFiles() by {
        reveal ValidFiles();
      }
      assert ValidDirs() by {
        reveal ValidDirs();
      }
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
    method {:timeLimitMultiplier 2} allocFile(txn: Txn) returns (ok: bool, ino: Ino)
      modifies Repr
      requires Valid() ensures Valid()
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

    method CreateFile(txn: Txn, d_ino: Ino, name: PathComp)
      returns (ok: bool, ino: Ino)
      modifies Repr
      requires Valid() ensures ok ==> Valid()
      requires fs.fs.has_jrnl(txn)
      ensures ok ==>
      && old(is_dir(d_ino))
      && old(is_invalid(ino))
      && data == old(
        var d := data[d_ino].dir;
        var d' := DirFile(d[name := ino]);
        data[ino := File.empty][d_ino := d'])
    {
      var err, dents := readDirents(txn, d_ino);
      if err.IsError() {
        ok := false;
        return;
      }
      ok, ino := allocFile(txn);
      if !ok {
        return;
      }
      assert ino_ok: ino !in old(data);
      if dents.findName(name) < 128 {
        // TODO: support creating a file and overwriting existing (rather than
        // failing here)
        ok := false;
        return;
      }
      var i := dents.findFree();
      if !(i < 128) {
        // no space in directory
        ok := false;
        return;
      }
      var e' := DirEnt(name, ino);
      dents.insert_ent_dir(e');
      ghost var d := dents.dir;
      dents := dents.insert_ent(i, e');
      ghost var d' := dents.dir;
      assert d' == d[name := ino];
      ok := writeDirents(txn, d_ino, dents);
      if !ok {
        return;
      }
      // assert data == old(data[ino := File.empty][d_ino := DirFile(d')]);
      reveal ino_ok;
    }

    method Stat(txn: Txn, ino: Ino)
      returns (ok: bool, r: StatRes)
      modifies fs.fs.fs
      requires Valid() ensures Valid()
      requires fs.fs.has_jrnl(txn)
      ensures !ok ==> ino !in data
      ensures ok ==>
          && ino in data
          && r.is_dir == data[ino].DirFile?
          && data[ino].ByteFile? ==> r.size as nat == |data[ino].data|
          && data[ino].DirFile? ==> r.size as nat == |data[ino].dir|
    {
      var i := startInode(txn, ino);
      if i.meta.ty.InvalidType? {
        assert is_invalid(ino) by { reveal is_of_type(); }
        fs.finishInodeReadonly(ino, i);
        assert ValidData() by {
          reveal ValidFiles();
        }
        ok := false;
        return;
      }
      ok := true;
      if i.meta.ty.DirType? {
        assert is_dir(ino) by { reveal is_of_type(); }
        var dents := readDirentsInode(txn, ino, i);
        fs.finishInodeReadonly(ino, i);
        assert Valid() by {
          assert ValidFiles() by { reveal ValidFiles(); }
        }
        var num_entries := dents.numValid();
        r := StatRes(true, num_entries);
        return;
      }
      // is a file
      assert i.meta.ty.FileType?;
      assert is_file(ino) by { reveal is_of_type(); }
      fs.finishInodeReadonly(ino, i);
      assert Valid() by {
        assert ValidFiles() by { reveal ValidFiles(); }
      }
      r := StatRes(false, i.sz);
      return;
    }

    // TODO:
    //
    // 1. Append
    // 2. Read
    // 3. CreateDir
    // 4. Write
    // 5. Rename (maybe?)
    // 6. Unlink

  }
}
