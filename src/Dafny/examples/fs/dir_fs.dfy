include "byte_fs.dfy"
include "dirent.dfy"

module DirFs
{
  import opened Machine
  import opened ByteSlice
  import opened Fs
  import opened FsKinds
  import opened JrnlTypes
  import opened JrnlSpec

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
    const rootIno: Ino

    const Repr: set<object> := {this} + fs.Repr

    static predicate alloc_ino_dom<T>(inode_owner: map<Ino, Option<()>>, m: map<Ino, T>)
      requires ino_dom(inode_owner)
    {
      forall ino:Ino :: ino in m <==> inode_owner[ino].Some?
    }

    predicate ValidDomains()
      requires fs.fs.Valid()
      reads Repr
    {
      && alloc_ino_dom(fs.fs.inode_owner(), data)
      && (forall ino:Ino :: ino in dirents <==>
        fs.inode_types()[ino].DirType?)
    }

    // TODO: make opaque
    predicate ValidRoot()
      reads Repr
      requires fs.fs.Valid()
    {
      // the root inode is allocated and is actually a directory
      && fs.fs.inode_owner()[rootIno].Some?
      && fs.inode_types()[rootIno].DirType?
      && rootIno != 0
    }

    predicate ValidDirents()
      requires fs.fs.Valid()
      reads Repr
    {
      forall ino:Ino | ino in dirents ::
        fs.data()[ino] == dirents[ino].enc()
    }

    predicate {:opaque} ValidFiles()
      requires fs.fs.Valid()
      reads Repr
    {
      forall ino:Ino | fs.fs.inode_owner()[ino].Some? && fs.inode_types()[ino].FileType? ::
           ino in data && data[ino] == ByteFile(fs.data()[ino])
    }

    predicate {:opaque} ValidDirs()
      requires fs.fs.Valid()
      reads Repr
    {

      && (forall ino:Ino | ino in dirents :: ino in data &&
        data[ino] == DirFile(dirents[ino].dir))
      && (forall ino:Ino :: fs.inode_types()[ino].DirType? ==>
        fs.fs.inode_owner()[ino].Some?)
    }

    predicate ValidData()
      requires fs.fs.Valid()
      reads Repr
    {
      && ValidFiles()
      && ValidDirs()
    }

    predicate ValidUnusedInodes()
      requires fs.fs.Valid()
      reads Repr
    {
      forall ino:Ino | fs.fs.inode_owner()[ino].None? ::
        fs.inode_types()[ino].FileType? && fs.data()[ino] == []
    }

    predicate ValidDirFs()
      requires fs.fs.Valid()
      reads Repr
    {
      && ValidDomains()
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

    constructor Init(fs: ByteFilesys<()>, rootIno: Ino)
      requires fs.Valid()
      requires fs.data() == map ino: Ino {:trigger} :: if ino == rootIno then Dirents.zero.enc() else []
      requires fs.inode_types() == map ino: Ino {:trigger} :: if ino == rootIno then Inode.DirType else Inode.FileType
      requires fs.fs.inode_owner() == map ino: Ino {:trigger} :: if ino == rootIno then Fs.Some(()) else Fs.None
      requires rootIno != 0
      ensures Valid()
      ensures data == map[rootIno := File.emptyDir]
    {
      this.fs := fs;
      this.rootIno := rootIno;
      var dirents0 : map<Ino, Dirents> := map[rootIno := Dirents.zero];
      this.dirents := dirents0;
      this.data := map[rootIno := File.emptyDir];
      new;
      Dirents.zero_dir();
      assert ValidData() by {
        reveal ValidFiles();
        reveal ValidDirs();
      }
    }

    static method allocEmptyDir(fs: ByteFilesys<()>, txn: Txn) returns (ok: bool, ino: Ino)
      modifies fs.Repr
      requires fs.Valid() ensures ok ==> fs.Valid()
      requires fs.fs.has_jrnl(txn)
      requires forall ino:Ino :: fs.data()[ino] == []
      ensures ok ==>
      && ino != 0
      && fs.data() == old(fs.data()[ino := Dirents.zero.enc()])
      && old(fs.fs.inode_owner()[ino].None?)
      && fs.fs.inode_owner() == old(fs.fs.inode_owner()[ino := Some(())])
      && fs.inode_types() == old(fs.inode_types()[ino := Inode.DirType])
    {
      ok, ino := fs.allocInode(txn, ());
      var ino0 := ino;
      if !ok {
        return;
      }

      assert fs.Valid();

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
      var ok, rootIno_ := allocEmptyDir(fs_, txn);
      if !ok {
        return None;
      }
      ok := txn.Commit();
      if !ok {
        return None;
      }
      assert fs_.Valid();

      var dir_fs := new DirFilesys.Init(fs_, rootIno_);
      return Some(dir_fs);
    }

    lemma alloc_ino_dom_not<T>(inode_owner: map<Ino, Option<()>>, m: map<Ino, T>, ino: Ino)
      requires ino_dom(inode_owner)
      requires alloc_ino_dom(inode_owner, m)
      requires !inode_owner[ino].Some?
      ensures ino !in m
    {}

    method {:timeLimitMultiplier 2} readDirents(txn: Txn, d_ino: Ino)
      returns (err: Error, dents: Dirents)
      modifies fs.fs.fs
      requires Valid() ensures Valid()
      requires fs.fs.has_jrnl(txn)
      ensures err.NoError? ==> d_ino in dirents && dents == dirents[d_ino]
      ensures err.DoesNotExist? ==> d_ino !in data
      ensures err.NotADir? ==> d_ino in data && data[d_ino].ByteFile?
      ensures !err.IsADir?
    {
      var i := fs.startInode(txn, d_ino);
      fs.inode_metadata(d_ino, i);
      var dir_exists? := fs.fs.fs.isInodeAllocated(txn, d_ino);
      if !dir_exists? {
        fs.finishInodeReadonly(d_ino, i);
        assert ValidData() by {
          reveal ValidFiles();
          reveal ValidDirs();
        }
        err := DoesNotExist;
        return;
      }
      if i.meta.ty == Inode.FileType {
        fs.finishInodeReadonly(d_ino, i);
        err := NotADir;
        reveal ValidFiles();
        reveal ValidDirs();
        return;
      }
      err := NoError;
      assert d_ino in dirents;

      assert |fs.data()[d_ino]| == 4096 by {
        dirents[d_ino].enc_len();
      }
      var bs := fs.readInternal(txn, d_ino, i, 0, 4096);
      fs.finishInodeReadonly(d_ino, i);
      dents := Dirents.decode(bs, dirents[d_ino]);
      assert ValidData() by {
        reveal ValidFiles();
        reveal ValidDirs();
      }
    }

    static method writeDirentsToFs(fs: ByteFilesys<()>, txn: Txn, d_ino: Ino, dents: Dirents)
      returns (ok:bool)
      modifies fs.Repr
      requires fs.Valid() ensures fs.Valid()
      requires fs.fs.has_jrnl(txn)
      requires |fs.data()[d_ino]| == 4096
      ensures fs.fs.inode_owner() == old(fs.fs.inode_owner())
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

    method {:timeLimitMultiplier 2} writeDirents(txn: Txn, d_ino: Ino, dents: Dirents)
      returns (ok:bool)
      modifies Repr
      requires fs.fs.has_jrnl(txn)
      requires Valid() ensures Valid()
      requires IsDir: d_ino in dirents
      ensures ok ==>
           && dirents == old(dirents[d_ino := dents])
           && data == old(data[d_ino := DirFile(dents.dir)])
    {
      assert |fs.data()[d_ino]| == 4096 by {
        reveal IsDir;
        dirents[d_ino].enc_len();
      }
      ok := writeDirentsToFs(fs, txn, d_ino, dents);
      if !ok {
        assert ValidData() by {
          reveal ValidFiles();
          reveal ValidDirs();
        }
        return;
      }

      dirents := dirents[d_ino := dents];
      data := data[d_ino := DirFile(dents.dir)];

      reveal IsDir;
      assert fs.inode_types()[d_ino].DirType?;
      assert ValidFiles() by {
        reveal ValidFiles();
      }
      assert ValidDirs() by {
        reveal ValidDirs();
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
      && ino !in old(data)
      && ino != 0
      && data == old(data[ino := File.empty])
      ensures !ok ==> data == old(data)
    {
      ok, ino := fs.allocInode(txn, ());
      if !ok {
        assert ValidData() by {
          reveal ValidFiles();
          reveal ValidDirs();
        }
        return;
      }
      data := data[ino := File.empty];
      assert ValidDirs() by {
        reveal ValidDirs();
      }
      assert ValidFiles() by {
        reveal ValidFiles();
      }
    }

    method CreateFile(txn: Txn, d_ino: Ino, name: PathComp)
      returns (ok: bool, ino: Ino)
      modifies Repr
      requires Valid() ensures ok ==> Valid()
      requires fs.fs.has_jrnl(txn)
      ensures ok ==>
      && d_ino in old(data) && old(data[d_ino].DirFile?)
      && ino !in old(data)
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
      assert d_ino_ok: d_ino in old(data) && old(data[d_ino].DirFile?) by {
        reveal ValidDirs();
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
      reveal d_ino_ok;
      reveal ino_ok;
    }

    method {:timeLimitMultiplier 2} Stat(txn: Txn, ino: Ino)
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
      var i := fs.startInode(txn, ino);
      fs.inode_metadata(ino, i);
      var file_exists? := fs.fs.fs.isInodeAllocated(txn, ino);
      if !file_exists? {
        fs.finishInodeReadonly(ino, i);
        assert ValidData() by {
          reveal ValidFiles();
          reveal ValidDirs();
        }
        ok := false;
        return;
      }
      ok := true;
      assert ino in data;
      var is_dir := i.meta.ty == Inode.DirType;
      assert is_dir == data[ino].DirFile? by {
        reveal ValidDirs();
        reveal ValidFiles();
      }
      if is_dir {
        assert |fs.data()[ino]| == 4096 by {
          dirents[ino].enc_len();
        }
        var bs := fs.readInternal(txn, ino, i, 0, 4096);
        fs.finishInodeReadonly(ino, i);
        var dents := Dirents.decode(bs, dirents[ino]);
        assert Valid() by {
          assert ValidData() by {
            reveal ValidFiles();
            reveal ValidDirs();
          }
        }
        var num_entries := dents.numValid();
        r := StatRes(true, num_entries);
        return;
      }
      // is a file
      fs.finishInodeReadonly(ino, i);
      r := StatRes(false, i.sz);
      assert ValidData() by {
        reveal ValidFiles();
        reveal ValidDirs();
      }
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
