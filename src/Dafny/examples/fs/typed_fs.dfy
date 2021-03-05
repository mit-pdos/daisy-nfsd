include "byte_fs.dfy"

module TypedFs {
  import opened ByteFs
  import opened FsKinds
  import opened JrnlTypes
  import opened JrnlSpec
  import opened Alloc
  import opened Machine
  import opened ByteSlice
  import Inode

  class TypedFilesys
  {
    ghost var data: map<Ino, seq<byte>>
    ghost var types: map<Ino, Inode.InodeType>
    const fs: ByteFilesys
    const ialloc: MaxAllocator

    ghost const Repr: set<object> := {this} + fs.Repr + ialloc.Repr;

    static const iallocMax: uint64 := super.num_inodes as uint64 - 8

    predicate {:opaque} bytefsValid()
      reads fs.Repr
    {
      // not quiescent
      && fs.fs.Valid()
    }

    predicate {:opaque} fsValidIno(ino: Ino, i: Inode.Inode)
      reads fs.Repr
    {
      && fs.fs.ValidIno(ino, i)
    }

    predicate {:opaque} ValidFields()
      reads Repr
      requires bytefsValid()
    {
      reveal bytefsValid();
      && data == fs.data()
      && types == fs.inode_types()
    }

    predicate ValidDomains()
      reads this
    {
      && Fs.ino_dom(data)
      && Fs.ino_dom(types)
    }

    predicate {:opaque} ValidInvalid()
      reads this
      requires ValidDomains()
    {
      forall ino: Ino :: types[ino].InvalidType? ==> data[ino] == []
    }

    predicate ValidAlloc()
      reads ialloc.Repr
    {
      && ialloc.Valid()
      && ialloc.max == iallocMax
      && ialloc.Repr !! fs.Repr
    }

    predicate ValidThis()
      reads Repr
      requires bytefsValid()
    {
      && ValidFields()
      && ValidDomains()
      && ValidInvalid()
      && ValidAlloc()
    }

    predicate Valid()
      reads Repr
    {
      && bytefsValid()
      && ValidThis()
      && fs.fs.fs.quiescent()
    }

    predicate ValidIno(ino: Ino, i: Inode.Inode)
      reads Repr
    {
      reveal fsValidIno();
      reveal bytefsValid();
      && fsValidIno(ino, i)
      && ValidThis()
    }

    constructor Init(d: Disk)
      ensures Valid()
      ensures fresh(Repr)
      ensures data == map ino:Ino {:trigger false} :: []
      ensures types == map ino:Ino {:trigger false} :: Inode.InvalidType
    {
      var fs_ := new ByteFilesys.Init(d);
      this.fs := fs_;
      this.data := fs_.data();
      this.types := fs_.inode_types();
      this.ialloc := new MaxAllocator(iallocMax);
      new;
      reveal bytefsValid();
      reveal ValidFields();
      reveal ValidInvalid();
    }

    twostate predicate types_unchanged()
      reads this
    {
      types == old(types)
    }

    predicate has_jrnl(txn: Txn)
      reads fs.fs.fs
    {
      fs.fs.has_jrnl(txn)
    }
  }
}
