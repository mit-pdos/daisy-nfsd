include "block_fs.dfy"
include "../../util/min_max.dfy"

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
  import opened MinMax
  import Round
  import Inode

  function {:opaque} raw_inode_data(d: InodeData): (bs:seq<byte>)
    ensures |bs| == Inode.MAX_SZ
  {
    C.concat_homogeneous_len(d.blks, 4096);
    C.concat(d.blks)
  }

  function inode_data(sz: nat, d: InodeData): (bs:seq<byte>)
    requires sz <= Inode.MAX_SZ
    ensures sz <= Inode.MAX_SZ && |bs| == sz as nat
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
      map ino:Ino | ino_ok(ino) ::
        (fs.metadata_bound(ino);
        inode_data(fs.metadata[ino], block_data(fs.data)[ino]))
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

    lemma raw_inode_index_one(d: InodeData, off: uint64)
      requires off % 4096 == 0
      requires off as nat + 4096 <= Inode.MAX_SZ
      ensures d.blks[off as nat/4096] == raw_inode_data(d)[off as nat..off as nat + 4096]
    {
      var blkoff := off as nat / 4096;
      C.concat_homogeneous_one_list(d.blks, blkoff, 4096);
      reveal raw_inode_data();
    }

    method alignedRead(txn: Txn, ino: Ino, i: Inode.Inode, off: uint64)
      returns (bs: Bytes)
      requires fs.ValidIno(ino, i)
      requires fs.has_jrnl(txn)
      requires off % 4096 == 0
      requires off as nat + 4096 <= Inode.MAX_SZ
      ensures bs.data == this.raw_data(ino)[off as nat..off as nat + 4096]
      ensures fresh(bs)
    {
      var blkoff: nat := off as nat / 4096;
      bs := BlockFs.Read(this.fs, txn, ino, i, blkoff);
      ghost var d := block_data(fs.data)[ino];
      assert bs.data == d.blks[blkoff];
      raw_inode_index_one(d, off);
    }

    method {:timeLimitMultiplier 2} readInternal(txn: Txn, ino: Ino, i: Inode.Inode, off: uint64, len: uint64)
      returns (bs: Bytes)
      requires fs.ValidIno(ino, i)
      requires fs.has_jrnl(txn)
      requires 0 < len <= 4096
      requires off as nat + len as nat <= |data()[ino]|
      ensures fresh(bs)
      ensures bs.data == this.data()[ino][off..off as nat +len as nat]
    {
      fs.inode_metadata(ino, i);
      var off' := off / 4096 * 4096;
      Arith.div_mod_split(off' as nat, 4096);
      assert off' + 4096 <= Inode.MAX_SZ_u64 by {
        Arith.div_incr(off' as nat, IndirectPos.config.total, 4096);
      }
      bs := alignedRead(txn, ino, i, off');
      if off' + 4096 >= off + len {
        // we finished the entire read
        bs.Subslice(off % 4096, off % 4096 + len);
        assert bs.data == raw_data(ino)[off as nat .. off as nat + len as nat] by {
          C.double_subslice_auto(raw_data(ino));
        }
        return;
      }

      // only keep data starting at off
      bs.Subslice(off % 4096, 4096);
      assert bs.data == raw_data(ino)[off as nat..off' + 4096] by {
        C.double_subslice_auto(raw_data(ino));
      }
      var read_bytes: uint64 := bs.Len();
      var off'' := off' + 4096;
      var bs2 := alignedRead(txn, ino, i, off'');
      bs2.Subslice(0, len - read_bytes);
      ghost var bs2_upper_bound: nat := off'' as nat + (len - read_bytes) as nat;
      assert bs2.data == raw_data(ino)[off''..bs2_upper_bound] by {
        C.double_subslice_auto(raw_data(ino));
      }

      bs.AppendBytes(bs2);
      assert (off + len) as nat == bs2_upper_bound;
      calc {
        bs.data;
        raw_data(ino)[off..off''] + raw_data(ino)[off''..bs2_upper_bound];
        raw_data(ino)[off..off + len];
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

      fs.inode_metadata(ino, i);

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

    method Size(ino: Ino) returns (sz: uint64)
      modifies fs.fs
      requires Valid() ensures Valid()
      requires ino_ok(ino)
      ensures data() == old(data())
      ensures sz as nat == |data()[ino]|
    {
      var txn := fs.fs.jrnl.Begin();
      var i := fs.startInode(txn, ino);
      sz := i.sz;
      fs.inode_metadata(ino, i);
      fs.finishInodeReadonly(ino, i);
      var _ := txn.Commit();
    }

    // private
    method alignedRawWrite(txn: Txn, ino: Ino, i: Inode.Inode, bs: Bytes, off: uint64)
      returns (ok: bool, i': Inode.Inode)
      modifies Repr()
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i')
      requires is_block(bs.data)
      requires off % 4096 == 0
      requires off as nat + 4096 <= Inode.MAX_SZ
      ensures bs.data == old(bs.data)
      ensures (var ino0 := ino;
        forall ino:Ino | ino_ok(ino) && ino != ino0 ::
          data()[ino] == old(data()[ino]))
      ensures ok ==> raw_data(ino) == C.splice(old(raw_data(ino)), off as nat, bs.data)
      ensures fs.metadata == old(fs.metadata)
      ensures !ok ==> raw_data(ino) == old(raw_data(ino))
      ensures !ok ==> data() == old(data())
    {
      i' := i;
      var blkoff: nat := off as nat / 4096;
      ok, i' := BlockFs.Write(fs, txn, ino, i, blkoff as nat, bs);
      if !ok {
        return;
      }
      ghost var d0 := old(block_data(fs.data)[ino]);
      ghost var d := block_data(fs.data)[ino];
      assert off as nat == blkoff * 4096;
      C.concat_homogeneous_len(d0.blks, 4096);
      assert d.blks == d0.blks[blkoff:=bs.data];
      ghost var blk: Block := bs.data;
      assert C.concat(d.blks) == C.splice(C.concat(d0.blks), off as nat, blk) by {
        C.concat_homogeneous_splice_one(d0.blks, blkoff, bs.data, 4096);
      }
      assert raw_data(ino) == C.splice(old(raw_data(ino)), off as nat, blk) by {
        reveal raw_inode_data();
        assert C.concat(d.blks) == raw_data(ino);
        assert C.concat(d0.blks) == old(raw_data(ino));
      }
    }

    // private
    method alignedWrite(txn: Txn, ino: Ino, i: Inode.Inode, bs: Bytes, off: uint64)
      returns (ok: bool, i': Inode.Inode)
      modifies Repr()
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i')
      requires is_block(bs.data)
      requires off % 4096 == 0
      requires off as nat + 4096 <= |data()[ino]|
      ensures bs.data == old(bs.data)
      ensures ok ==> data() == old(
      var d0 := data()[ino];
      var d := C.splice(d0, off as nat, bs.data);
      data()[ino := d])
      ensures !ok ==> data() == old(data())
    {
      i' := i;
      ok, i' := alignedRawWrite(txn, ino, i, bs, off);
      if !ok {
        return;
      }
      ghost var d0 := old(block_data(fs.data)[ino]);
      ghost var d := block_data(fs.data)[ino];
      C.concat_homogeneous_len(d0.blks, 4096);
      ghost var blk: Block := bs.data;
      ghost var sz := fs.metadata[ino];
      calc {
        inode_data(sz, d);
        raw_data(ino)[..sz];
        C.splice(old(raw_data(ino)), off as nat, blk)[..sz];
        { C.splice_prefix_comm(old(raw_data(ino)), off as nat, blk, sz); }
        C.splice(old(raw_data(ino))[..sz], off as nat, blk);
        C.splice(inode_data(sz, d0), off as nat, blk);
      }
      map_update_eq(old(data()), ino, inode_data(sz, d), data());
    }

    // private
    //
    // grow an inode with junk so that it can be filled with in-bounds writes
    method growBy(ghost ino: Ino, i: Inode.Inode, delta: uint64)
      returns (i': Inode.Inode, ghost junk: seq<byte>)
      modifies Repr()
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i')
      requires i.sz as nat + delta as nat <= Inode.MAX_SZ
      ensures |junk| == delta as nat
      ensures data() == old(data()[ino := data()[ino] + junk])
    {
      fs.inode_metadata(ino, i);
      ghost var sz := i.sz;
      var sz' := i.sz + delta;
      i' := fs.writeInodeSz(ino, i, sz');
      fs.inode_metadata(ino, i');
      assert raw_data(ino) == old(raw_data(ino));
      junk := raw_data(ino)[sz..sz'];
      assert data()[ino] == old(data()[ino] + junk) by {
        reveal raw_inode_data();
      }
    }

    method shrinkTo(ghost ino: Ino, i: Inode.Inode, sz': uint64)
      returns (i': Inode.Inode)
      modifies Repr()
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i')
      requires sz' <= i.sz
      ensures sz' as nat <= old(|data()[ino]|)
      ensures data() == old(data()[ino := data()[ino][..sz' as nat]])
    {
      fs.inode_metadata(ino, i);
      i' := fs.writeInodeSz(ino, i, sz');
      fs.inode_metadata(ino, i');
      assert raw_data(ino) == old(raw_data(ino));
      assert data()[ino] == old(data()[ino][..sz' as nat]) by {
        reveal raw_inode_data();
      }
    }

    /*
    lemma data_append_at_end(data: seq<byte>, junk: seq<byte>, bs: seq<byte>)
      requires (
      var sz := |data|;
      var remaining_space := 4096 - sz % 4096;
      var written := |bs|;
      var sz' := |data| + written;
      && sz % 4096 != 0
      && |junk| == remaining_space
      && |bs| <= remaining_space
      )
      ensures (
      var sz := |data|;
      var data0 := data;
      var data1 := data0 + junk;
      var off' := sz / 4096 * 4096;
      var blk := C.splice(data1[off'..off' + 4096], sz % 4096, bs);
      var data2 := C.splice(data1, off' as nat, blk);
      var data3 := data2[..|data0| + |bs|];
      data3 == data0 + bs
      )
    {
      assume false;
    }
    */

    lemma data_append_at_end(data0: seq<byte>, junk: seq<byte>, bs: seq<byte>,
      data1: seq<byte>, blk: seq<byte>, data2: seq<byte>, data3: seq<byte>)
      requires (
      var sz := |data0|;
      var remaining_space := 4096 - sz % 4096;
      var off' := sz / 4096 * 4096;
      && sz % 4096 != 0
      && |junk| == remaining_space
      && |bs| <= remaining_space
      && data1 == data0 + junk
      && blk == C.splice(data1[off'..off' + 4096], sz % 4096, bs)
      && data2 == C.splice(data1, off' as nat, blk)
      && data3 == data2[..|data0| + |bs|]
      )
      ensures data3 == data0 + bs
    {
      assume false;
    }

    // private
    method appendAtEnd(txn: Txn, ino: Ino, i: Inode.Inode, bs: Bytes)
      returns (ok: bool, i': Inode.Inode, ghost written: nat, bs': Bytes)
      modifies Repr(), bs
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i')
      requires bs.Valid()
      requires i.sz as nat + |bs.data| <= Inode.MAX_SZ
      requires 0 < |bs.data| <= 4096
      ensures written <= old(|bs.data|)
      ensures ok ==> (
      && bs'.Valid()
      && (bs'.Len() == 0 ==> written == old(|bs.data|))
      && (bs'.Len() != 0 ==> i'.sz % 4096 == 0 && written < old(|bs.data|)))
      ensures ok ==> data() == old(data()[ino := data()[ino] + bs.data[..written]])
      ensures !ok ==> data == old(data)
    {
      i' := i;
      if i.sz % 4096 == 0 {
        ok := true;
        // sz is already aligned
        written := 0;
        bs' := bs;
        assert data()[ino] + bs.data[..written] == data()[ino];
        return;
      }

      var remaining_space := 4096 - i.sz % 4096;
      var to_write: uint64 := min_u64(remaining_space, bs.Len());
      var desired_size: uint64 := i.sz + to_write;
      assert desired_size as nat <= i.sz as nat + remaining_space as nat;
      ghost var data0 := data()[ino];
      written := to_write as nat;
      ghost var junk;
      fs.inode_metadata(ino, i');
      i', junk := this.growBy(ino, i', remaining_space);
      fs.inode_metadata(ino, i');
      ghost var data1 := data()[ino];
      assert data1 == data0 + junk;

      bs' := bs.Split(to_write);
      Round.roundup_distance(i.sz as nat, 4096);
      var blkoff: uint64 := i.sz / 4096;
      var off': uint64 := blkoff * 4096;
      Arith.mul_mod(blkoff as nat, 4096);
      assert off' as nat + 4096 <= Inode.MAX_SZ;
      var blk := this.alignedRead(txn, ino, i', off');
      assert blk.data == data1[off' as nat..off' as nat + 4096];
      assert |bs.data| <= remaining_space as nat;
      blk.CopyTo(i.sz % 4096, bs);
      ok, i' := this.alignedWrite(txn, ino, i', blk, off');
      if !ok {
        return;
      }
      fs.inode_metadata(ino, i');
      ghost var data2 := data()[ino];
      assert data2 == C.splice(data1, off' as nat, blk.data);
      i' := shrinkTo(ino, i', desired_size);
      ghost var data3 := data()[ino];
      assert data3 == data2[..i.sz as nat + written];
      assert data3 == data0 + bs.data by {
        assert |data0| == i.sz as nat;
        assert off' as nat == i.sz as nat / 4096 * 4096;
        assert |data0| + |bs.data| == desired_size as nat;
        assume false;
        assert blk.data == C.splice(data1[off'..off' + 4096], i.sz as nat % 4096, bs.data);
        data_append_at_end(data0, junk, bs.data,
          data1, blk.data, data2, data3);
      }
    }

    // public
    method {:timeLimitMultiplier 2} Append(ino: Ino, bs: Bytes, off: uint64) returns (ok:bool)
      modifies Repr(), bs
      requires Valid() ensures Valid()
      requires ino_ok(ino)
      requires bs.Valid()
      requires bs.Len() <= 4096
      ensures ok ==> data() == old(data()[ino := data()[ino] + bs.data])
    {
      var txn := fs.fs.jrnl.Begin();
      var i := fs.startInode(txn, ino);
      if i.sz + bs.Len() >= Inode.MAX_SZ_u64 {
        ok := false;
        fs.finishInodeReadonly(ino, i);
        return;
      }

      if bs.Len() == 0 {
        ok := true;
        assert bs.data == [];
        assert data()[ino] == data()[ino] + bs.data;
        fs.finishInodeReadonly(ino, i);
        var _ := txn.Commit();
        return;
      }

      // TODO: call appendAtEnd to align existing data
      //
      // TODO: if appendAtEnd leaves nothing to write, return and prove postcondition
      //
      // TODO: implement appendAligned to extend inode size, write new data
      // extended to full block, and shrink back (overall effect is to append)

      assume false;
      fs.finishInode(txn, ino, i);
      var _ := txn.Commit();
    }

  }
}
