include "byte_fs.dfy"

module TypedFs {
  import opened Std

  import opened ByteFs
  import opened FsKinds
  import opened JrnlTypes
  import opened JrnlSpec
  import opened Machine
  import opened ByteSlice
  import Inode
  import opened MemInodes

  predicate is_read_data(data: seq<byte>, off: nat, len: nat,
    bs: seq<byte>, eof: bool)
  {
    && |bs| <= len
    && (off + |bs| <= |data| ==> bs == data[off..off + |bs|])
    && (eof <==> off + |bs| >= |data|)
  }

  class TypedFilesys
  {
    ghost var data: map<Ino, seq<byte>>
    ghost var types: map<Ino, Inode.InodeType>
    const fs: ByteFilesys
    const ialloc: Allocator

    ghost const Repr: set<object> := {this} + fs.Repr;

    static const iallocMax: uint64 := super.num_inodes as uint64

    predicate {:opaque} bytefsValid()
      reads fs.Repr
    {
      // not quiescent
      && fs.fs.Valid()
    }

    predicate {:opaque} fsValidIno(ino: Ino, i: MemInode)
      reads fs.Repr, i.Repr
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
    {
      && ialloc.Valid()
      && ialloc.max == iallocMax
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

    predicate ValidIno(ino: Ino, i: MemInode)
      reads Repr, i.Repr
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
      var ialloc := NewAllocator(iallocMax);
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

    method startInode(txn: Txn, ino: Ino) returns (ok: bool, i': MemInode)
      modifies fs.fs.fs
      requires Valid()
      ensures ok ==> ValidIno(ino, i')
      ensures !ok ==> Valid()
      requires has_jrnl(txn)
      ensures ok ==> inode_unchanged(ino, i'.val())
      ensures fresh(i'.Repr)
      ensures ok ==> i'.ty == types[ino]
      ensures !ok ==> old(types[ino].InvalidType?)
    {
      reveal_valids();
      i' := fs.startInode(txn, ino);
      fs.inode_metadata(ino, i');
      if i'.ty.InvalidType? {
        ok := false;
        fs.finishInodeReadonly(ino, i');
        reveal ValidFields();
        return;
      }
      ok := true;
      reveal ValidFields();
    }

    ghost method finishInodeReadonly(ino: Ino, i: MemInode)
      modifies fs.fs.fs
      requires ValidIno(ino, i)
      requires inode_unchanged(ino, i.val())
      ensures Valid()
    {
      reveal_valids();
      fs.finishInodeReadonly(ino, i);
      reveal ValidFields();
    }

    method finishInode(txn: Txn, ino: Ino, i: MemInode)
      modifies fs.Repr, i.bs
      requires has_jrnl(txn)
      requires ValidIno(ino, i)
      ensures Valid()
    {
      reveal_valids();
      fs.finishInode(txn, ino, i);
      reveal ValidFields();
    }

    lemma inode_metadata(ino: Ino, i: MemInode)
      requires ValidIno(ino, i)
      ensures i.ty == types[ino]
      ensures i.sz as nat == |data[ino]|
    {
      fs.inode_metadata(ino, i);
      reveal ValidFields();
    }

    method allocInode(txn: Txn, ty: Inode.InodeType) returns (ok: bool, ino: Ino, i: MemInode?)
      modifies Repr
      requires Valid()
      requires has_jrnl(txn)
      requires !ty.InvalidType?
      ensures ok ==> i != null && fresh(i.Repr)
      ensures ok ==>
      && old(types[ino].InvalidType?) && types == old(types[ino := ty])
      && data == old(data)
      && data[ino] == []
      && ValidIno(ino, i)
      && ino != 0
    {
      reveal_valids();
      ino := ialloc.Alloc();
      if ino == 0 {
        ok := false;
        return;
      }
      i := fs.startInode(txn, ino);
      fs.inode_metadata(ino, i);
      if !i.ty.InvalidType? {
        ok := false;
        return;
      }
      ok := true;
      fs.setType(ino, i, ty);
      types := fs.inode_types();
      reveal ValidInvalid();
      reveal ValidFields();
    }

    method allocateAt(txn: Txn, ino: Ino, ty: Inode.InodeType) returns (i': MemInode)
      modifies Repr
      requires Valid() ensures ValidIno(ino, i')
      requires has_jrnl(txn)
      requires !ty.InvalidType?
      requires types[ino] == Inode.InvalidType
      ensures data == old(data)
      ensures data[ino] == []
      ensures types == old(types[ino := ty])
      ensures fresh(i'.Repr)
    {
      reveal_valids();
      i' := fs.startInode(txn, ino);
      fs.inode_metadata(ino, i');
      fs.setType(ino, i', ty);
      types := fs.inode_types();
      reveal ValidInvalid();
      reveal ValidFields();
    }

    method freeSafe(ino: Ino)
        requires ValidAlloc()
        requires ino_ok(ino)
    {
        if ino as uint64 == 0 {
            return;
        }
        ialloc.Free(ino);
    }

    method freeInode(txn: Txn, ino: Ino, i: MemInode)
      modifies Repr, i.Repr
      requires has_jrnl(txn)
      requires ValidIno(ino, i) ensures Valid()
      ensures data == old(data[ino := []])
      ensures types == old(types[ino := Inode.InvalidType])
    {
      reveal_valids();
      fs.setType(ino, i, Inode.InvalidType);
      fs.shrinkToEmpty(txn, ino, i);
      fs.finishInode(txn, ino, i);
      freeSafe(ino);
      data := fs.data();
      types := fs.inode_types();
      reveal ValidFields();
      reveal ValidInvalid();
    }

    method writeBlock(txn: Txn, ino: Ino, i: MemInode, off: uint64, bs: Bytes)
      returns (ok: bool)
      modifies Repr, i.Repr
      requires has_jrnl(txn)
      requires ValidIno(ino, i) ensures ok ==> ValidIno(ino, i)
      requires bs !in i.Repr
      requires |bs.data| == 4096
      requires off % 4096 == 0
      requires off as nat + 4096 <= |data[ino]|
      ensures ok ==>
      data == old(data[ino := C.splice(data[ino], off as nat, bs.data)])
      ensures types_unchanged()
    {
      reveal ValidFields();
      ok := fs.alignedWrite(txn, ino, i, bs, off);
      data := fs.data();
      reveal ValidInvalid();
    }

    method writeOne_(txn: Txn, ino: Ino, i: MemInode, off: uint64, bs: Bytes)
      returns (ok: bool)
      modifies Repr, bs, i.Repr
      requires ValidIno(ino, i) ensures ok ==> ValidIno(ino, i)
      requires bs !in i.Repr
      requires has_jrnl(txn)
      requires 0 < |bs.data| <= 4096
      requires off as nat <= |data[ino]|
      requires off as nat + |bs.data| <= Inode.MAX_SZ
      ensures ok ==>
      && data == old(data[ino := write_data(data[ino], off as nat, bs.data)])
      ensures types_unchanged()
    {
      reveal ValidFields();
      ok := fs.write(txn, ino, i, off, bs);
      if !ok {
        return;
      }
      data := fs.data();
      assert ValidIno(ino, i) by {
        reveal ValidInvalid();
      }
    }

    method {:timeLimitMultiplier 2} write(txn: Txn, ino: Ino, i: MemInode, off: uint64, bs: Bytes)
      returns (ok: bool)
      modifies Repr, bs, i.Repr
      requires ValidIno(ino, i) ensures ok ==> ValidIno(ino, i)
      requires bs !in i.Repr
      requires has_jrnl(txn)
      requires 0 < |bs.data| <= 6*4096
      requires off as nat <= |data[ino]|
      requires off as nat + |bs.data| <= Inode.MAX_SZ
      ensures ok ==>
      && data == old(data[ino := write_data(data[ino], off as nat, bs.data)])
      ensures types_unchanged()
    {
      reveal ValidFields();
      ghost var data0 := bs.data;
      ghost var original_bs := bs;
      var bs := bs;
      var written: uint64 := 0 as uint64;
      assert data0[..written as nat] == [];
      assert write_data(data[ino], off as nat, []) == data[ino];

      while bs.Len() > 4096
        decreases |bs.data|
        invariant fresh({bs} - {original_bs})
        invariant 0 < |bs.data| <= |data0| <= 6*4096
        invariant ValidIno(ino, i)
        invariant bs !in i.Repr
        invariant written as nat <= |data0|
        invariant bs.data == data0[written..]
        invariant data == old(data[ino := write_data(data[ino], off as nat, data0[..written])])
        invariant types_unchanged()
      {
        write_data_app(data[ino], off as nat,
          // already written
          data0[..written],
          // newly written
          data0[written..written + 4096]);
        assert data0[..written] + data0[written..written + 4096] == data0[..written + 4096];
        assert |data0[..written]| == written as nat;
        var bs_remaining := bs.Split(4096);
        assert bs.data == data0[written..written + 4096];
        ok := writeOne_(txn, ino, i, off + written, bs);
        if !ok {
          return;
        }
        assert data[ino] == old(write_data(data[ino], off as nat, data0[..written + 4096]));
        bs := bs_remaining;
        written := written + 4096;
      }

      write_data_app(data[ino], off as nat,
        data0[..written], data0[written..]);
      assert data0 == data0[..written] + data0[written..];
      assert |data0[..written]| == written as nat;
      ok := writeOne_(txn, ino, i, off + written, bs);
      if !ok {
        return;
      }
      assert data[ino] == old(write_data(data[ino], off as nat, data0));
    }

    method writeBlockFile(txn: Txn, ino: Ino, i: MemInode, bs: Bytes)
      returns (ok: bool)
      modifies Repr, i.Repr
      requires ValidIno(ino, i) ensures ok ==> ValidIno(ino, i)
      requires bs !in i.Repr
      requires has_jrnl(txn)
      requires is_block(bs.data)
      requires |data[ino]| == 4096
      ensures types_unchanged()
      ensures ok ==> && data == old(data[ino := bs.data])
    {
      reveal ValidFields();
      C.splice_all(data[ino], bs.data);
      ok := fs.alignedWrite(txn, ino, i, bs, 0);
      data := fs.data();
      reveal ValidInvalid();
    }

    method readUnsafe(txn: Txn, ino: Ino, i: MemInode, off: uint64, len: uint64)
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

    method read(txn: Txn, ino: Ino, i: MemInode, off: uint64, len: uint64)
      returns (bs: Bytes, ok: bool, eof: bool)
      modifies fs.fs.fs
      requires has_jrnl(txn)
      requires ValidIno(ino, i) ensures ValidIno(ino, i)
      ensures fs.fs.fs.cur_inode == old(fs.fs.fs.cur_inode)
      requires inode_unchanged(ino, i.val())
      requires len <= 4096
      ensures fresh(bs)
      ensures ok ==> is_read_data(data[ino], off as nat, len as nat, bs.data, eof)
    {
      if sum_overflows(off, len) {
        bs := NewBytes(0);
        ok := false;
        return;
      }
      inode_metadata(ino, i);
      if off > i.sz {
        bs := NewBytes(0);
        ok := true;
        eof := true;
        return;
      }
      var readLen: uint64 := len;
      if off + len >= i.sz {
        readLen := i.sz - off;
        eof := true;
      } else {
        eof := false;
      }
      bs, ok := fs.readWithInode(txn, ino, i, off, readLen);
      reveal ValidFields();
    }

    method setSize(txn: Txn, ghost ino: Ino, i: MemInode, sz': uint64)
      returns (ghost junk: seq<byte>)
      modifies Repr, i.Repr
      requires ValidIno(ino, i) ensures ValidIno(ino, i)
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
      junk := fs.setSize(txn, ino, i, sz');
      data := fs.data();
      reveal ValidFields();
      reveal ValidInvalid();
    }

  }
}
