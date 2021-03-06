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

    static const iallocMax: uint64 := super.num_inodes as uint64

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
      && !types[ino].InvalidType?
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
      var ialloc := new MaxAllocator(iallocMax);
      // the root inode
      ialloc.MarkUsed(1);
      this.ialloc := ialloc;
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

    predicate inode_unchanged(ino: Ino, i: Inode.Inode)
      reads fs.fs.fs
    {
      fs.fs.fs.cur_inode == Some((ino, i))
    }

    method startInode(txn: Txn, ino: Ino) returns (ok: bool, i': Inode.Inode)
      modifies fs.fs.fs
      requires Valid() ensures ok ==> ValidIno(ino, i')
      requires has_jrnl(txn)
      ensures inode_unchanged(ino, i')
      ensures !ok ==> old(types[ino].InvalidType?)
      ensures ok ==> i'.meta.ty == types[ino]
    {
      reveal_valids();
      i' := fs.startInode(txn, ino);
      fs.inode_metadata(ino, i');
      if i'.meta.ty.InvalidType? {
        ok := false;
        reveal ValidFields();
        return;
      }
      ok := true;
      reveal ValidFields();
    }

    ghost method finishInodeReadonly(ino: Ino, i: Inode.Inode)
      modifies fs.fs.fs
      requires ValidIno(ino, i)
      requires inode_unchanged(ino, i)
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
      requires !ty.InvalidType?
      ensures ok ==>
      && old(types[ino].InvalidType?) && types == old(types[ino := ty])
      && data == old(data)
      && data[ino] == []
      && ValidIno(ino, i)
      && ino != 0
    {
      reveal_valids();
      ino := ialloc.Alloc();
      i := fs.startInode(txn, ino);
      fs.inode_metadata(ino, i);
      if !i.meta.ty.InvalidType? {
        ok := false;
        return;
      }
      i := fs.setType(ino, i, ty);
      types := fs.inode_types();
      reveal ValidInvalid();
      reveal ValidFields();
    }

    method allocateAt(txn: Txn, ino: Ino, ty: Inode.InodeType) returns (i': Inode.Inode)
      modifies Repr
      requires Valid() ensures ValidIno(ino, i')
      requires has_jrnl(txn)
      requires !ty.InvalidType?
      requires types[ino] == Inode.InvalidType
      ensures data == old(data)
      ensures data[ino] == []
      ensures types == old(types[ino := ty])
    {
      reveal_valids();
      i' := fs.startInode(txn, ino);
      fs.inode_metadata(ino, i');
      i' := fs.setType(ino, i', ty);
      types := fs.inode_types();
      reveal ValidInvalid();
      reveal ValidFields();
    }


    method freeInode(txn: Txn, ino: Ino, i: Inode.Inode)
      modifies Repr
      requires has_jrnl(txn)
      requires ValidIno(ino, i) ensures Valid()
      ensures data == old(data[ino := []])
      ensures types == old(types[ino := Inode.InvalidType])
    {
      reveal_valids();
      var i := fs.setType(ino, i, Inode.InvalidType);
      i := fs.shrinkToEmpty(txn, ino, i);
      fs.finishInode(txn, ino, i);
      ialloc.Free(ino);
      data := fs.data();
      types := fs.inode_types();
      reveal ValidFields();
      reveal ValidInvalid();
    }

    method append(txn: Txn, ino: Ino, i: Inode.Inode, bs: Bytes)
      returns (ok: bool, i': Inode.Inode)
      modifies Repr, bs
      requires ValidIno(ino, i) ensures ok ==> ValidIno(ino, i')
      requires has_jrnl(txn)
      requires 0 < |bs.data| <= 4096
      requires |data[ino]| + |bs.data| <= Inode.MAX_SZ
      ensures ok ==>
      && data == old(data[ino := data[ino] + bs.data])
      ensures types_unchanged()
    {
      reveal ValidFields();
      ok, i' := fs.appendIno(txn, ino, i, bs);
      data := fs.data();
      reveal ValidInvalid();
    }

    method writeBlockFile(txn: Txn, ino: Ino, i: Inode.Inode, bs: Bytes)
      returns (ok: bool, i': Inode.Inode)
      modifies Repr
      requires ValidIno(ino, i) ensures ok ==> ValidIno(ino, i')
      requires has_jrnl(txn)
      requires is_block(bs.data)
      requires |data[ino]| == 4096
      ensures types_unchanged()
      ensures ok ==> && data == old(data[ino := bs.data])
    {
      reveal ValidFields();
      C.splice_all(data[ino], bs.data);
      ok, i' := fs.alignedWrite(txn, ino, i, bs, 0);
      data := fs.data();
      reveal ValidInvalid();
    }

    method readUnsafe(txn: Txn, ino: Ino, i: Inode.Inode, off: uint64, len: uint64)
      returns (bs: Bytes)
      requires ValidIno(ino, i)
      requires has_jrnl(txn)
      requires 0 < len <= 4096
      requires off as nat + len as nat <= |data[ino]|
      ensures fresh(bs)
      ensures bs.data == this.data[ino][off..off as nat + len as nat]
    {
      reveal ValidFields();
      bs := fs.readInternal(txn, ino, i, off, len);
    }

    method read(txn: Txn, ino: Ino, i: Inode.Inode, off: uint64, len: uint64)
      returns (bs: Bytes, ok: bool)
      modifies fs.fs.fs
      requires has_jrnl(txn)
      requires ValidIno(ino, i) ensures Valid()
      requires inode_unchanged(ino, i)
      requires len <= 4096
      ensures ok ==>
          && off as nat + len as nat <= |data[ino]|
          && bs.data == this.data[ino][off..off as nat + len as nat]
    {
      bs, ok := fs.readWithInode(txn, ino, i, off, len);
      reveal ValidFields();
    }

    method setSize(txn: Txn, ghost ino: Ino, i: Inode.Inode, sz': uint64)
      returns (i': Inode.Inode, ghost junk: seq<byte>)
      modifies Repr
      requires ValidIno(ino, i) ensures ValidIno(ino, i')
      requires has_jrnl(txn)
      requires sz' as nat <= Inode.MAX_SZ
      ensures
      (var d0 := old(data[ino]);
      var d' := ByteFs.ByteFilesys.setSize_with_junk(d0, sz' as nat, junk);
      && data == old(data[ino := d']))
      ensures
      (var d0 := old(data[ino]);
      && sz' as nat > |d0| ==> |junk| == sz' as nat - |d0|)
      ensures types_unchanged()
    {
      i', junk := fs.setSize(txn, ino, i, sz');
      data := fs.data();
      reveal ValidFields();
      reveal ValidInvalid();
    }

  }
}
