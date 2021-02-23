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
      && forall ino:Ino :: ino in dirents <==>
        (fs.fs.inode_owner()[ino].Some? && fs.inode_types()[ino].DirType?)
    }

    predicate ValidDirents()
      reads Repr
    {
      // relate fs.data() to dirents
      true
    }

    predicate Valid()
      reads Repr
    {
      && fs.Valid()
      && ValidDomains()
    }

    constructor Init(d: Disk)
      ensures Valid()
    {
      fs := new ByteFilesys.Init(d);
      dirents := map[];
      data := map[];
    }
  }
}
