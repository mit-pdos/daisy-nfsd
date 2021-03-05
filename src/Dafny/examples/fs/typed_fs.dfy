include "byte_fs.dfy"

module TypedFs {
  import opened Std

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

    lemma reveal_valids()
      ensures bytefsValid() == fs.fs.Valid()
      ensures forall ino:Ino, i :: fsValidIno(ino, i) == fs.fs.ValidIno(ino, i)
    {
      reveal bytefsValid();
      reveal fsValidIno();
    }

    predicate {:opaque} ValidFields()
      reads this, fs.Repr
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

    predicate inode_unmodified(ino: Ino, i: Inode.Inode)
      reads fs.fs.fs
    {
      fs.fs.fs.cur_inode == Some((ino, i))
    }

    method startInode(txn: Txn, ino: Ino) returns (i': Inode.Inode)
      modifies fs.fs.fs
      requires has_jrnl(txn)
      requires Valid() ensures ValidIno(ino, i')
      ensures inode_unmodified(ino, i')
    {
      reveal_valids();
      i' := fs.startInode(txn, ino);
      reveal ValidFields();
    }

    ghost method finishInodeReadonly(ino: Ino, i: Inode.Inode)
      modifies fs.fs.fs
      requires ValidIno(ino, i)
      requires inode_unmodified(ino, i)
      ensures Valid()
    {
      reveal_valids();
      fs.finishInodeReadonly(ino, i);
      reveal ValidFields();
    }

    method finishInode(txn: Txn, ino: Ino, i: Inode.Inode)
      modifies fs.Repr
      requires has_jrnl(txn)
      requires ValidIno(ino, i)
      ensures Valid()
    {
      reveal_valids();
      fs.finishInode(txn, ino, i);
      reveal ValidFields();
    }

    lemma inode_metadata(ino: Ino, i: Inode.Inode)
      requires ValidIno(ino, i)
      ensures i.meta.ty == types[ino]
      ensures i.meta.sz as nat == |data[ino]|
    {
      fs.inode_metadata(ino, i);
      reveal ValidFields();
    }

    method allocInode(txn: Txn, ty: Inode.InodeType) returns (ok: bool, ino: Ino, i: Inode.Inode)
      modifies Repr
      requires Valid()
      requires has_jrnl(txn)
      ensures ok ==>
      && old(types[ino].InvalidType?) && types == old(types[ino := ty])
      && data == old(data)
      && data[ino] == []
      && ValidIno(ino, i)
    {
      ino := ialloc.Alloc();
      i := startInode(txn, ino);
      inode_metadata(ino, i);
      if !i.meta.ty.InvalidType? {
        ok := false;
        return;
      }
      i := fs.setType(ino, i, ty);
      types := fs.inode_types();
      reveal ValidInvalid();
      reveal ValidFields();
    }

    // todo
      // fs.alignedWrite
      // fs.appendIno
      // fs.readInternal
      // fs.readWithInode
      // fs.setSize
      // fs.shrinkToEmpty

  }
}
