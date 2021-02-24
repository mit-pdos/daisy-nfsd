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
      requires fs.Valid()
      reads Repr
    {
      && alloc_ino_dom(fs.fs.inode_owner(), data)
      && (forall ino:Ino :: ino in dirents <==>
        (fs.fs.inode_owner()[ino].Some? && fs.inode_types()[ino].DirType?))
    }

    predicate ValidRoot()
      reads Repr
      requires fs.Valid()
    {
      // the root inode is allocated and is actually a directory
      && fs.fs.inode_owner()[rootIno].Some?
      && fs.inode_types()[rootIno].DirType?
      && rootIno != 0
    }

    predicate ValidDirents()
      requires fs.Valid()
      reads Repr
    {
      forall ino:Ino | ino in dirents ::
        fs.data()[ino] == dirents[ino].enc()
    }

    predicate {:opaque} ValidFiles()
      requires fs.Valid()
      reads Repr
    {
      forall ino:Ino | fs.fs.inode_owner()[ino].Some? && fs.inode_types()[ino].FileType? ::
           ino in data && data[ino] == ByteFile(fs.data()[ino])
    }

    predicate {:opaque} ValidDirs()
      requires fs.Valid()
      reads Repr
    {

      forall ino:Ino | ino in dirents :: ino in data && data[ino] == DirFile(dirents[ino].dir)
    }

    predicate ValidData()
      requires fs.Valid()
      reads Repr
    {
      && ValidFiles()
      && ValidDirs()
    }

    predicate ValidUnusedInodes()
      requires fs.Valid()
      reads Repr
    {
      forall ino:Ino | fs.fs.inode_owner()[ino].None? ::
        fs.inode_types()[ino].FileType? && fs.data()[ino] == []
    }


    predicate Valid()
      reads Repr
    {
      && fs.Valid()
      && ValidDomains()
      && ValidRoot()
      && ValidDirents()
      && ValidData()
      && ValidUnusedInodes()
    }

    constructor Init(fs: ByteFilesys<()>, rootIno: Ino)
      requires fs.Valid()
      requires fs.data() == map ino: Ino {:trigger} :: if ino == rootIno then Dirents.zero.enc() else []
      requires fs.inode_types() == map ino: Ino {:trigger} :: if ino == rootIno then Inode.DirType else Inode.FileType
      requires fs.fs.inode_owner() == map ino: Ino {:trigger} :: if ino == rootIno then Fs.Some(()) else Fs.None
      requires rootIno != 0
      ensures Valid()
      ensures data == map[rootIno := DirFile(map[])]
    {
      this.fs := fs;
      this.rootIno := rootIno;
      var dirents0 : map<Ino, Dirents> := map[rootIno := Dirents.zero];
      this.dirents := dirents0;
      this.data := map[rootIno := DirFile(map[])];
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
  }
}
