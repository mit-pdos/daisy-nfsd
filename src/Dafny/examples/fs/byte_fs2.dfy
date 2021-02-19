include "block_fs.dfy"

module ByteFs {
  import Fs
  import opened BlockFs
  import IndirectPos
  import opened IndFs
  import opened FsKinds
  import opened JrnlTypes
  import opened JrnlSpec
  import opened Machine
  import opened ByteSlice
  import Inode

  function num_used(sz: nat): nat
  {
    sz / 4096
  }

  function {:opaque} raw_inode_data(d: InodeData): (bs:seq<byte>)
    ensures |bs| == 4096*Inode.MAX_SZ
  {
    C.concat_homogeneous_len(d.blks, 4096);
    C.concat(d.blks)
  }

  function inode_data(sz: nat, d: InodeData): (bs:seq<byte>)
    requires sz <= Inode.MAX_SZ
    ensures |bs| == sz as nat
  {
    raw_inode_data(d)[..sz]
  }

  class ByteFilesys
  {
    const fs: IndFilesys;

    function Repr(): set<object>
    {
      fs.Repr()
    }

    predicate Valid()
      reads this.Repr()
    {
      && fs.ValidQ()
    }

    function data(): map<Ino, seq<byte>>
      reads Repr()
      requires fs.Valid()
    {
      map ino:Ino | ino_ok(ino) :: inode_data(fs.metadata[ino], block_data(fs.data)[ino])
    }

    function raw_data(ino: Ino): seq<byte>
      reads Repr()
      requires ino_ok(ino)
      requires fs.Valid()
    {
      raw_inode_data(block_data(fs.data)[ino])
    }

    constructor Init(d: Disk)
      ensures Valid()
      ensures data() == map ino: Ino | ino_ok(ino) :: []
    {
      var the_fs := BlockFs.New(d);
      this.fs := the_fs;
      new;
    }

    method {:timeLimitMultiplier 2} alignedRead(txn: Txn, ino: Ino, i: Inode.Inode, off: uint64)
      returns (bs: Bytes)
      requires fs.ValidIno(ino, i)
      requires fs.has_jrnl(txn)
      requires off % 4096 == 0
      requires off as nat + 4096 <= 4096*Inode.MAX_SZ
      ensures bs.data == this.raw_data(ino)[off as nat..off as nat + 4096]
      ensures fresh(bs)
    {
      var blkoff: nat := (off/4096) as nat;
      bs := BlockFs.Read(this.fs, txn, ino, i, blkoff);
      ghost var d := block_data(fs.data)[ino];
      assert bs.data == d.blks[blkoff];
      C.concat_homogeneous_one_list(d.blks, blkoff, 4096);
      assert off as nat == 4096*blkoff;
      assert off as nat + 4096 == 4096*blkoff + 4096;
      // TODO: this is super slow even though it matches the postcondition of
      // C.concat_homogeneous_one_list, up to congruence
      assert d.blks[blkoff] == C.concat(d.blks)[off as nat..off as nat + 4096];
      // TODO: this is slow even with the above assumed
      assert bs.data == this.raw_data(ino)[off as nat..off as nat + 4096] by {
        reveal raw_inode_data();
      }
    }

    method readInternal(txn: Txn, ino: Ino, i: Inode.Inode, off: uint64, len: uint64)
      returns (bs: Bytes)
      requires fs.ValidIno(ino, i)
      requires fs.has_jrnl(txn)
      requires 0 < len
      requires off as nat + len as nat <= |data()[ino]|
      ensures fresh(bs)
      ensures bs.data == this.data()[ino][off..off+len]
    {
      var off' := off / 4096 * 4096;
      assert off' + 4096 <= 4096*Inode.MAX_SZ_u64 by {
        Arith.div_incr(off' as nat, Inode.MAX_SZ, 4096);
      }
      bs := alignedRead(txn, ino, i, off');
      assume false;
      if off' + 4096 >= off + len {
        // we finished the entire read
        bs.Subslice(off % 4096, off % 4096 + len);
        fs.finishInodeReadonly(ino, i);
        var _ := txn.Commit();
        C.double_subslice_auto(data()[ino]);
        return;
      }
    }

    // TODO: why is this so slow?
    method {:timeLimitMultiplier 2} Read(ino: Ino, off: uint64, len: uint64)
      returns (bs: Bytes, ok: bool)
      modifies fs.fs
      requires Valid() ensures Valid()
      requires ino_ok(ino)
      ensures ok ==>
          && off as nat + len as nat <= |data()[ino]|
          && bs.data == this.data()[ino][off..off+len]
    {
      if len > 4096 {
        ok := false;
        bs := NewBytes(0);
        return;
      }
      var txn := fs.fs.jrnl.Begin();
      var i := fs.startInode(txn, ino);

      if sum_overflows(off, len) || off+len > i.sz {
        ok := false;
        bs := NewBytes(0);
        fs.finishInodeReadonly(ino, i);
        return;
      }
      assert off as nat + len as nat <= |data()[ino]|;

      ok := true;
      if len == 0 {
        bs := NewBytes(0);
        fs.finishInodeReadonly(ino, i);
        calc {
          this.data()[ino][off..off+len];
          { assert off+len == off; }
          this.data()[ino][off..off];
          [];
          bs.data;
        }
        return;
      }
      assert 0 < len <= 4096;
      bs := readInternal(txn, ino, i, off, len);
      fs.finishInodeReadonly(ino, i);
      assert data() == old(data());
      var _ := txn.Commit();
    }

  }
}
