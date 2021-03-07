include "block_fs.dfy"
include "../../util/min_max.dfy"

module ByteFs {
  import opened Std
  import Fs
  import IndirectPos
  import opened FsKinds
  import opened JrnlTypes
  import opened JrnlSpec
  import opened Machine
  import opened ByteSlice
  import opened MinMax
  import Round

  import opened BlockFs
  import opened IndFs
  import opened MemInodes
  import Inode

  function {:opaque} raw_inode_data(d: InodeData): (bs:seq<byte>)
    ensures |bs| == Inode.MAX_SZ
  {
    C.concat_homogeneous_len(d.blks, 4096);
    C.concat(d.blks)
  }

  lemma splice_zero_raw_inode_data(blks: seq<Block>, off: nat, count: nat)
    requires off + count <= |blks|
    ensures |C.concat(blks)| == |blks|*4096
    ensures C.concat(C.splice(blks, off, C.repeat(block0, count))) ==
            C.splice(C.concat(blks), off*4096, C.repeat(0 as byte, count*4096))
  {
    C.concat_homogeneous_len(blks, 4096);
    var zeroblks := C.repeat(block0, count);

    calc {
      C.concat(C.splice(blks, off, zeroblks));
      C.concat(blks[..off] + zeroblks + blks[off + count..]);
      { C.concat_app(blks[..off] + zeroblks, blks[off + count..]);
        C.concat_app(blks[..off], zeroblks); }
      C.concat(blks[..off]) + C.concat(zeroblks) + C.concat(blks[off + count..]);
      { C.concat_homogeneous_prefix(blks, off, 4096); }
      C.concat(blks)[..off*4096] + C.concat(zeroblks) + C.concat(blks[off + count..]);
      { C.concat_homogeneous_suffix(blks, off+count, 4096); }
      C.concat(blks)[..off*4096] + C.concat(zeroblks) + C.concat(blks)[(off + count)*4096..];
    }

    assert C.concat(zeroblks) == C.repeat(0 as byte, count*4096) by {
      assert block0 == C.repeat(0 as byte, 4096);
      assert zeroblks == C.repeat(C.repeat(0 as byte, 4096), count);
      C.concat_repeat(0 as byte, 4096, count);
    }

    //C.concat_homogeneous_prefix(blks, off, 4096);
    //C.concat_homogeneous_suffix(blks, off+count, 4096);
  }

  function inode_data(sz: nat, d: InodeData): (bs:seq<byte>)
    requires sz <= Inode.MAX_SZ
    ensures sz <= Inode.MAX_SZ && |bs| == sz as nat
  {
    raw_inode_data(d)[..sz]
  }

  // less general than actual WRITE semantics, which also supports creating
  // holes by first extending data to make off in bounds
  function write_data(data: seq<byte>, off: nat, bs: seq<byte>): seq<byte>
    requires off <= |data|
  {
    data[..off] + bs + if off + |bs| <= |data| then data[off + |bs|..] else []
  }

  lemma write_data_splice(data: seq<byte>, off: nat, bs: seq<byte>)
    requires off + |bs| <= |data|
    ensures write_data(data, off, bs) == C.splice(data, off, bs)
  {}

  lemma write_data_to_end(data: seq<byte>, off: nat, bs: seq<byte>)
    requires off + |bs| == |data|
    ensures write_data(data, off, bs) == data[..off] + bs
  {}

  lemma write_data_append(data: seq<byte>, off: nat, bs: seq<byte>)
    requires off == |data|
    ensures write_data(data, off, bs) == data + bs
  {}

  lemma write_data_past_end(data: seq<byte>, off: nat, bs: seq<byte>)
    requires off <= |data|
    requires off + |bs| > |data|
    ensures write_data(data, off, bs) == data[..off] + bs
  {}

  class ByteFilesys
  {
    const fs: IndFilesys
    ghost const Repr: set<object> := fs.Repr

    predicate Valid()
      reads this.Repr
    {
      && fs.ValidQ()
    }

    function data(): map<Ino, seq<byte>>
      reads Repr
      requires fs.Valid()
    {
      map ino:Ino ::
        (fs.metadata_bound(ino);
        inode_data(fs.metadata[ino].sz as nat, block_data(fs.data)[ino]))
    }

    function {:opaque} inode_types(): (m:map<Ino, Inode.InodeType>)
      reads fs
      requires Fs.ino_dom(fs.metadata)
      ensures Fs.ino_dom(m)
    {
      map ino: Ino :: fs.metadata[ino].ty
    }

    twostate predicate types_unchanged()
      reads fs
      requires old(Fs.ino_dom(fs.metadata)) && Fs.ino_dom(fs.metadata)
    {
      inode_types() == old(inode_types())
    }

    twostate lemma inode_types_metadata_unchanged()
      requires old(Fs.ino_dom(fs.metadata)) && Fs.ino_dom(fs.metadata)
      requires fs.metadata == old(fs.metadata)
      ensures types_unchanged()
    {
      reveal inode_types();
    }

    function raw_data(ino: Ino): seq<byte>
      reads Repr
      requires fs.Valid()
    {
      raw_inode_data(block_data(fs.data)[ino])
    }

    constructor Init(d: Disk)
      ensures Valid()
      ensures fresh(Repr)
      ensures data() == map ino: Ino {:trigger} :: []
      ensures inode_types() == map ino: Ino {:trigger} :: Inode.InvalidType
    {
      var the_fs := BlockFs.New(d);
      this.fs := the_fs;
      new;
      reveal inode_types();
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

    method alignedRead(txn: Txn, ino: Ino, i: MemInode, off: uint64)
      returns (bs: Bytes)
      requires fs.ValidIno(ino, i)
      requires fs.has_jrnl(txn)
      requires off % 4096 == 0
      requires off as nat + 4096 <= Inode.MAX_SZ
      ensures bs.data == this.raw_data(ino)[off as nat..off as nat + 4096]
      ensures fresh(bs)
    {
      var blkoff: uint64 := off / 4096;
      bs := BlockFs.Read(this.fs, txn, ino, i, blkoff);
      ghost var d := block_data(fs.data)[ino];
      assert bs.data == d.blks[blkoff];
      raw_inode_index_one(d, off);
    }

    method {:timeLimitMultiplier 2} readInternal(txn: Txn, ino: Ino, i: MemInode, off: uint64, len: uint64)
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

    method readWithInode(txn: Txn, ino: Ino, i: MemInode, off: uint64, len: uint64)
      returns (bs: Bytes, ok: bool)
      modifies fs.fs
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) && fs.fs.cur_inode == Some( (ino, i.val()) )
      ensures Valid()
      requires len <= 4096
      ensures fresh(bs)
      ensures ok ==>
          && off as nat + len as nat <= |data()[ino]|
          && bs.data == this.data()[ino][off..off+len]
    {
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
    }

    method readTxn(txn: Txn, ino: Ino, off: uint64, len: uint64)
      returns (bs: Bytes, ok: bool)
      modifies fs.fs
      requires fs.has_jrnl(txn)
      requires Valid() ensures Valid()
      ensures ok ==>
          && off as nat + len as nat <= |data()[ino]|
          && bs.data == this.data()[ino][off..off+len]
    {
      if len > 4096 {
        ok := false;
        bs := NewBytes(0);
        return;
      }
      var i := fs.startInode(txn, ino);
      bs, ok := readWithInode(txn, ino, i, off, len);
    }

    // public
    method Read(ino: Ino, off: uint64, len: uint64)
      returns (bs: Bytes, ok: bool)
      modifies fs.fs
      requires Valid() ensures Valid()
      ensures ok ==>
          && off as nat + len as nat <= |data()[ino]|
          && bs.data == this.data()[ino][off..off+len]
      ensures data() == old(data())
    {
      var txn := fs.fs.jrnl.Begin();
      bs, ok := readTxn(txn, ino, off, len);
      // TODO: this is read-only, no need to commit the transaction
      var _ := txn.Commit();
    }

    // public
    method Size(ino: Ino) returns (sz: uint64)
      modifies fs.fs
      requires Valid() ensures Valid()
      ensures data() == old(data())
      ensures sz as nat == |data()[ino]|
    {
      var txn := fs.fs.jrnl.Begin();
      var i := fs.startInode(txn, ino);
      sz := i.sz;
      fs.inode_metadata(ino, i);
      fs.finishInodeReadonly(ino, i);
      // TODO: this is read-only, no need to commit the transaction
      var _ := txn.Commit();
    }

    // private
    method alignedRawWrite(txn: Txn, ino: Ino, i: MemInode, bs: Bytes, off: uint64)
      returns (ok: bool)
      modifies Repr, i.Repr
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i)
      requires is_block(bs.data)
      requires off % 4096 == 0
      requires off as nat + 4096 <= Inode.MAX_SZ
      ensures bs.data == old(bs.data)
      ensures (var ino0 := ino;
        forall ino:Ino | ino != ino0 ::
          data()[ino] == old(data()[ino]))
      ensures ok ==> raw_data(ino) == C.splice(old(raw_data(ino)), off as nat, bs.data)
      ensures fs.metadata == old(fs.metadata)
      ensures types_unchanged()
      ensures !ok ==> raw_data(ino) == old(raw_data(ino))
      ensures !ok ==> data() == old(data())
    {
      var blkoff: uint64 := off / 4096;
      var wh := new BlockFs.WriteHelper(fs);
      ok := wh.Do(txn, ino, i, blkoff, bs);
      assert types_unchanged() by {
        reveal inode_types();
      }
      if !ok {
        return;
      }
      ghost var d0 := old(block_data(fs.data)[ino]);
      ghost var d := block_data(fs.data)[ino];
      assert off as nat == blkoff as nat * 4096;
      C.concat_homogeneous_len(d0.blks, 4096);
      assert d.blks == d0.blks[blkoff:=bs.data];
      ghost var blk: Block := bs.data;
      assert C.concat(d.blks) == C.splice(C.concat(d0.blks), off as nat, blk) by {
        C.concat_homogeneous_splice_one(d0.blks, blkoff as nat, bs.data, 4096);
      }
      assert raw_data(ino) == C.splice(old(raw_data(ino)), off as nat, blk) by {
        reveal raw_inode_data();
        assert C.concat(d.blks) == raw_data(ino);
        assert C.concat(d0.blks) == old(raw_data(ino));
      }
      inode_types_metadata_unchanged();
    }

    // private
    method alignedWrite(txn: Txn, ino: Ino, i: MemInode, bs: Bytes, off: uint64)
      returns (ok: bool)
      modifies Repr, i.Repr
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i)
      requires is_block(bs.data)
      requires off % 4096 == 0
      requires off as nat + 4096 <= |data()[ino]|
      ensures bs.data == old(bs.data)
      ensures fs.metadata == old(fs.metadata);
      ensures types_unchanged()
      ensures ok ==> data() == old(
      var d0 := data()[ino];
      var d := C.splice(d0, off as nat, bs.data);
      data()[ino := d])
      ensures !ok ==> data() == old(data())
    {
      ok := alignedRawWrite(txn, ino, i, bs, off);
      inode_types_metadata_unchanged();
      if !ok {
        return;
      }
      ghost var d0 := old(block_data(fs.data)[ino]);
      ghost var d := block_data(fs.data)[ino];
      C.concat_homogeneous_len(d0.blks, 4096);
      ghost var blk: Block := bs.data;
      ghost var sz := fs.metadata[ino].sz as nat;
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
    method growBy(ghost ino: Ino, i: MemInode, delta: uint64)
      returns (ghost junk: seq<byte>)
      modifies Repr, i.Repr
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i)
      requires i.sz as nat + delta as nat <= Inode.MAX_SZ
      ensures |junk| == delta as nat
      ensures data() == old(data()[ino := data()[ino] + junk])
      ensures types_unchanged()
    {
      fs.inode_metadata(ino, i);
      ghost var sz := i.sz;
      var sz' := i.sz + delta;
      fs.writeInodeMeta(ino, i, Inode.Meta(sz', i.ty));
      fs.inode_metadata(ino, i);
      assert raw_data(ino) == old(raw_data(ino));
      junk := raw_data(ino)[sz..sz'];
      assert data()[ino] == old(data()[ino] + junk) by {
        reveal raw_inode_data();
      }
      assert types_unchanged() by {
        reveal inode_types();
      }
    }

    method freeRangeRaw(txn: Txn, ghost ino: Ino, i: MemInode, off: uint64, len: uint64)
      returns (ok: bool)
      modifies Repr, i.Repr
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i)
      requires off % 4096 == 0 && len % 4096 == 0 && off as nat + len as nat <= Inode.MAX_SZ
      ensures (var ino0 := ino;
        forall ino:Ino | ino != ino0 ::
          data()[ino] == old(data()[ino]))
      ensures ok ==> raw_data(ino) == old(C.splice(raw_data(ino), off as nat, C.repeat(0 as byte, len as nat)))
      ensures !ok ==> data() == old(data()) && raw_data(ino) == old(raw_data(ino))
      ensures fs.metadata == old(fs.metadata)
      ensures types_unchanged()
    {
      if off + len <= 10 * 4096 {
        ok := true;
        var startblk: uint64 := off / 4096;
        var count: uint64 := len / 4096;
        var h := new BlockFs.ZeroHelper(fs);
        h.Do(txn, ino, i, startblk, count);
        inode_types_metadata_unchanged();
        assert raw_data(ino) ==
          old(C.splice(raw_data(ino), off as nat,
              C.repeat(0 as byte, len as nat))) by {
          reveal raw_inode_data();
          splice_zero_raw_inode_data(old(block_data(fs.data)[ino].blks), startblk as nat, count as nat);
          assert startblk*4096 == off;
          assert count*4096 == len;
        }
        return;
      }
      ok := false;
      return;
    }

    method {:timeLimitMultiplier 2} shrinkTo(txn: Txn, ghost ino: Ino, i: MemInode, sz': uint64)
      modifies Repr, i.Repr
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i)
      requires sz' <= i.sz
      ensures sz' as nat <= old(|data()[ino]|)
      ensures data() == old(data()[ino := data()[ino][..sz' as nat]])
      ensures types_unchanged()
    {
      fs.inode_metadata(ino, i);
      var unusedStart := Round.roundup64(sz', 4096);
      var unusedEnd := Round.roundup64(i.sz, 4096);
      Round.roundup_incr(sz' as nat, i.sz as nat, 4096);
      var ok;
      ok := this.freeRangeRaw(txn, ino, i, unusedStart, unusedEnd - unusedStart);

      fs.inode_metadata(ino, i);
      fs.writeInodeMeta(ino, i, Inode.Meta(sz', i.ty));
      fs.inode_metadata(ino, i);
      assert data()[ino] == old(data()[ino][..sz' as nat]) by {
        reveal raw_inode_data();
      }
      assert types_unchanged() by {
        reveal inode_types();
      }
    }

    method shrinkToEmpty(txn: Txn, ghost ino: Ino, i: MemInode)
      modifies Repr, i.Repr
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i)
      ensures data() == old(data()[ino := []])
      ensures types_unchanged()
    {
      this.shrinkTo(txn, ino, i, 0);
    }

    static function setSize_with_junk(data: seq<byte>, sz: nat, junk: seq<byte>): seq<byte>
    {
      if sz <= |data| then data[..sz] else data + junk
    }

    method setSize(txn: Txn, ghost ino: Ino, i: MemInode, sz': uint64)
      returns (ghost junk: seq<byte>)
      modifies Repr, i.Repr
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i)
      requires sz' as nat <= Inode.MAX_SZ
      ensures
      (var d0 := old(data()[ino]);
      var d' := setSize_with_junk(d0, sz' as nat, junk);
      && data() == old(data()[ino := d']))
      ensures
      (var d0 := old(data()[ino]);
      sz' as nat > |d0| ==> |junk| == sz' as nat - |d0|)
      ensures types_unchanged()
    {
      fs.inode_metadata(ino, i);
      assert i.sz as nat == |data()[ino]|;
      if sz' <= i.sz {
         this.shrinkTo(txn, ino, i, sz');
      } else {
        junk := this.growBy(ino, i, sz' - i.sz);
      }
    }

    lemma data_update_in_place(data0: seq<byte>, data1: seq<byte>, off: nat, bs: seq<byte>, blk: seq<byte>)
      requires off + |bs| <= off/4096*4096 + 4096 <= |data0|
      requires
      (var off' := off / 4096 * 4096;
      && blk == C.splice(data0[off'..off'+4096], off % 4096, bs)
      && data1 == C.splice(data0, off', blk)
      )
      ensures data1 == C.splice(data0, off, bs)
    {
      var off' := off / 4096 * 4096;
      assert data1 == C.splice(data0, off', blk);
      assert off == off' + off % 4096;
      forall i: nat | i < |data0|
        ensures C.splice(data0, off', blk)[i] == C.splice(data0, off, bs)[i]
      {
        C.splice_get_i(data0, off, bs, i);
        C.splice_get_i(data0, off', blk, i);
        if i < off' || i > off' + 4096 {}
        else {
          if 0 <= i - off' < 4096 {
            C.splice_get_i(blk, off % 4096, bs, i - off');
          }
        }
      }
      assert data1 == C.splice(data0, off, bs);
    }

    method {:timeLimitMultiplier 3} updateInPlace(txn: Txn, ino: Ino, i: MemInode, off: uint64, bs: Bytes)
      returns (ok: bool)
      modifies Repr, i.Repr
      requires bs !in i.Repr
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i)
      requires 0 < |bs.data| <= 4096
      requires off as nat + |bs.data| <= |data()[ino]|
      requires off as nat % 4096 + |bs.data| <= 4096
      ensures types_unchanged()
      ensures ok ==> data() == old(
      var d0 := data()[ino];
      var d := C.splice(d0, off as nat, bs.data);
      data()[ino := d])
    {
      if bs.Len() == 4096 {
        ok := this.alignedWrite(txn, ino, i, bs, off);
        inode_types_metadata_unchanged();
        return;
      }
      ghost var d0 := data()[ino];
      assert |data()[ino]| <= Inode.MAX_SZ;
      var aligned_off: uint64 := off / 4096 * 4096;
      //assert aligned_off as nat + off as nat % 4096 == off as nat;
      //assert aligned_off as nat + 4096 <= Inode.MAX_SZ;
      var blk := this.alignedRead(txn, ino, i, aligned_off);
      blk.CopyTo(off % 4096, bs);
      ok := this.alignedRawWrite(txn, ino, i, blk, aligned_off);
      if !ok {
        return;
      }
      fs.inode_metadata(ino, i);
      assert raw_data(ino) == C.splice(old(raw_data(ino)), off as nat, bs.data);
      calc {
        data()[ino];
        raw_data(ino)[..i.sz];
        { C.splice_prefix_comm(old(raw_data(ino)), off as nat, bs.data, i.sz as nat); }
        C.splice(d0, off as nat, bs.data);
      }
      inode_types_metadata_unchanged();
    }

    method {:timeLimitMultiplier 2} overwrite(txn: Txn, ino: Ino, i: MemInode, off: uint64, bs: Bytes)
      returns (ok: bool)
      modifies Repr, bs, i.Repr
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i)
      requires bs !in i.Repr
      requires |bs.data| <= 4096
      requires off as nat + |bs.data| <= |data()[ino]|
      ensures types_unchanged()
      ensures ok ==> data() == old(
      var d0 := data()[ino];
      var d := C.splice(d0, off as nat, bs.data);
      data()[ino := d])
    {
      ghost var d0 := data()[ino];
      if bs.Len() == 0 {
        assert bs.data == [];
        assert C.splice(d0, off as nat, bs.data) == d0;
        return;
      }
      if off % 4096 + bs.Len() <= 4096 {
        ok := updateInPlace(txn, ino, i, off, bs);
        return;
      }
      var len1 := 4096 - off % 4096;
      var bs' := bs.Split(len1);
      assert bs.data + bs'.data == old(bs.data);
      ok := updateInPlace(txn, ino, i, off, bs);
      if !ok {
        return;
      }
      var off' := off + len1;
      ok := updateInPlace(txn, ino, i, off', bs');
      if !ok {
        return;
      }
      ghost var d := data()[ino];
      calc {
        d;
        C.splice(C.splice(d0, off as nat, bs.data), off' as nat, bs'.data);
        C.splice(d0, off as nat, bs.data + bs'.data);
      }
    }

    // private
    method {:timeLimitMultiplier 2} appendAtEnd(txn: Txn, ino: Ino, i: MemInode, bs: Bytes)
      returns (ok: bool, ghost written: nat, bs': Bytes)
      modifies Repr, bs, i.Repr
      requires fs.has_jrnl(txn)
      requires bs !in i.Repr
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i)
      requires bs.Valid()
      requires i.sz as nat + |bs.data| <= Inode.MAX_SZ
      requires 0 < |bs.data| <= 4096
      ensures written <= old(|bs.data|)
      // we don't make this abstract because it's needed to guarantee progress
      ensures written == old(min(4096 - |data()[ino]| % 4096, |bs.data|))
      ensures ok ==> fresh(bs') && bs'.Valid() && bs'.data == old(bs.data[written..])
      ensures ok ==> data() == old(data()[ino := data()[ino] + bs.data[..written]])
      ensures !ok ==> data == old(data)
      ensures types_unchanged()
    {
      fs.inode_metadata(ino, i);
      var sz0 := i.sz;

      var remaining_space := 4096 - sz0 % 4096;
      ghost var data0 := data()[ino];
      ghost var junk;
      junk := this.growBy(ino, i, remaining_space);
      ghost var data1 := data()[ino];
      assert data1 == data0 + junk;
      assert bs.data == old(bs.data);

      var to_write: uint64 := min_u64(remaining_space, bs.Len());
      var desired_size: uint64 := sz0 + to_write;
      assert desired_size as nat <= sz0 as nat + remaining_space as nat;
      written := to_write as nat;

      bs' := bs.Split(to_write);
      assert bs.data == old(bs.data[..written]);
      assert bs' !in i.Repr;
      fs.inode_metadata(ino, i);
      Round.roundup_distance(sz0 as nat, 4096);
      ok := this.updateInPlace(txn, ino, i, sz0, bs);
      if !ok {
        return;
      }
      if bs'.Len() == 0 {
        assert written == old(|bs.data|);
        assert old(bs.data[..written]) == old(bs.data);
      }
      fs.inode_metadata(ino, i);
      ghost var data2 := data()[ino];
      assert desired_size as nat == sz0 as nat + to_write as nat;

      shrinkTo(txn, ino, i, desired_size);
      ghost var data3 := data()[ino];

      assert |data3| == |data0| + written;
      assert data3[..|data0|] == data0;
      assert data3[|data0|..] == bs.data;
      calc {
        data3;
        data3[..|data0|] + data3[|data0|..];
        data0 + bs.data;
      }
      assert data() == old(data()[ino := data()[ino] + bs.data[..written]]);
    }

    method alignedAppend(txn: Txn, ino: Ino, i: MemInode, bs: Bytes)
      returns (ok: bool)
      modifies Repr, bs, i.Repr
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i)
      requires bs !in i.Repr
      requires bs.Valid()
      requires i.sz as nat + |bs.data| <= Inode.MAX_SZ
      requires 0 < |bs.data| <= 4096
      requires |data()[ino]| % 4096 == 0
      ensures ok ==> data() == old(data()[ino := data()[ino] + bs.data])
      ensures !ok ==> data == old(data)
      ensures types_unchanged()
    {
      ghost var written;
      var bs';
      ok, written, bs' := appendAtEnd(txn, ino, i, bs);
      assert written == old(|bs.data|);
      assert old(bs.data[..written]) == old(bs.data);
    }

    method {:timeLimitMultiplier 2} appendIno(txn: Txn, ino: Ino, i: MemInode, bs: Bytes)
      returns (ok:bool)
      modifies Repr, bs, i.Repr
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i)
      requires bs !in i.Repr
      requires 0 < |bs.data| <= 4096
      requires |data()[ino]| + |bs.data| <= Inode.MAX_SZ
      ensures ok ==> data() == old(data()[ino := data()[ino] + bs.data])
      ensures types_unchanged()
    {
      fs.inode_metadata(ino, i);
      ghost var sz0 := i.sz as nat;

      ghost var written;
      var bs';
      ok, written, bs' := this.appendAtEnd(txn, ino, i, bs);
      assert types_unchanged();
      if !ok {
        // TODO: we should really just abort here
        return;
      }
      if bs'.Len() == 0 {
        assert old(bs.data[..written]) == old(bs.data);
        return;
      }
      fs.inode_metadata(ino, i);
      assert i.sz as nat + |bs'.data| == sz0 + old(|bs.data|) by {
        assert old(|bs.data[..written]|) == written;
        assert |bs'.data| == old(|bs.data|) - written;
        assert |data()[ino]| == old(|data()[ino]|) + written;
      }
      assert |data()[ino]| % 4096 == 0;

      ok := this.alignedAppend(txn, ino, i, bs');
      assert types_unchanged();
      if !ok {
        // TODO: we should really just abort here
        return;
      }
      ghost var first_write := old(bs.data[..written]);
      ghost var leftovers := old(bs.data[written..]);
      assert data()[ino] == old(data()[ino] + bs.data) by {
        calc {
          data()[ino];
          { C.app_assoc(old(data()[ino]), first_write, leftovers); }
          old(data()[ino]) + (first_write + leftovers);
          { C.split_rejoin(old(bs.data), written); }
          old(data()[ino]) + old(bs.data);
        }
      }
    }

    method write(txn: Txn, ino: Ino, i: MemInode, off: uint64, bs: Bytes)
      returns (ok: bool)
      modifies Repr, bs, i.Repr
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i)
      requires bs !in i.Repr
      requires 0 < |bs.data| <= 4096
      requires off as nat <= |data()[ino]|
      requires off as nat + |bs.data| <= Inode.MAX_SZ
      ensures types_unchanged()
      ensures ok ==>
      && data() == old(
      var d0 := data()[ino];
      var d := write_data(d0, off as nat, bs.data);
      data()[ino := d])
    {
      ghost var d0 := data()[ino];
      fs.inode_metadata(ino, i);
      assert |d0| == i.sz as nat;
      if off + bs.Len() <= i.sz {
        // all in place
        ok := this.overwrite(txn, ino, i, off, bs);
        return;
      }
      if off == i.sz {
        write_data_append(d0, off as nat, bs.data);
        ok := this.appendIno(txn, ino, i, bs);
        return;
      }
      write_data_past_end(d0, off as nat, bs.data);
      // need to write some
      var bs' := bs.Split(i.sz - off);
      ghost var bs1 := bs.data;
      ghost var bs2 := bs'.data;
      assert bs1 + bs2 == old(bs.data);
      ok := this.overwrite(txn, ino, i, off, bs);
      if !ok {
        return;
      }
      assert data()[ino] == d0[..off as nat] + bs1;
      ok := this.appendIno(txn, ino, i, bs');
      if !ok {
        return;
      }
      calc {
        data()[ino];
        d0[..off as nat] + bs1 + bs2;
        d0[..off as nat] + (bs1 + bs2);
      }
    }

    // public
    //
    // this variant can be used in a larger transaction
    method append_txn(txn: Txn, ino: Ino, bs: Bytes)
      returns (ok:bool)
      modifies Repr, bs
      requires fs.has_jrnl(txn)
      requires Valid() ensures Valid()
      requires bs.Valid()
      requires bs.Len() <= 4096
      ensures ok ==> data() == old(data()[ino := data()[ino] + bs.data])
      ensures types_unchanged()
    {
      var i := fs.startInode(txn, ino);
      if i.sz + bs.Len() > Inode.MAX_SZ_u64 {
        ok := false;
        fs.finishInodeReadonly(ino, i);
        inode_types_metadata_unchanged();
        return;
      }

      if bs.Len() == 0 {
        ok := true;
        assert bs.data == [];
        assert data()[ino] == data()[ino] + bs.data;
        fs.finishInodeReadonly(ino, i);
        inode_types_metadata_unchanged();
        return;
      }

      fs.inode_metadata(ino, i);
      ok := this.appendIno(txn, ino, i, bs);
      fs.finishInode(txn, ino, i);
      assert types_unchanged() by {
        reveal inode_types();
      }
      return;
    }

    // public
    method Append(ino: Ino, bs: Bytes) returns (ok:bool)
      modifies Repr, bs
      requires Valid() ensures Valid()
      requires bs.Valid()
      requires bs.Len() <= 4096
      ensures ok ==> data() == old(data()[ino := data()[ino] + bs.data])
    {
      var txn := fs.fs.jrnl.Begin();
      ok := append_txn(txn, ino, bs);
      if !ok {
        // abort
        txn.Abort();
        return;
      }
      ok := txn.Commit();
    }

    method setType(ghost ino: Ino, i: MemInode, ty': Inode.InodeType)
      modifies Repr, i.Repr
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i)
      ensures data() == old(data())
      ensures inode_types() == old(inode_types()[ino := ty'])
    {
      fs.inode_metadata(ino, i);
      fs.writeInodeMeta(ino, i, Inode.Meta(i.sz, ty'));
      assert block_data(fs.data) == old(block_data(fs.data));
      assert data() == old(data()) by {
        reveal raw_inode_data();
        assert raw_data(ino) == old(raw_data(ino));
        assert fs.metadata[ino].sz == old(fs.metadata[ino].sz);
      }
      reveal inode_types();
    }

    method startInode(txn: Txn, ino: Ino) returns (i: MemInode)
      modifies fs.fs
      requires fs.has_jrnl(txn)
      requires Valid() ensures fs.ValidIno(ino, i)
      ensures fs.fs.cur_inode == Some( (ino, i.val()) )
      ensures data() == old(data())
      ensures types_unchanged()
      ensures fresh(i.Repr)
    {
      i := fs.startInode(txn, ino);
      assert types_unchanged() by {
        reveal inode_types();
      }
    }

    lemma inode_metadata(ino: Ino, i: MemInode)
      requires fs.ValidIno(ino, i)
      ensures i.ty == inode_types()[ino]
      ensures i.sz as nat == |data()[ino]|
    {
      fs.inode_metadata(ino, i);
      reveal inode_types();
    }

    method finishInode(txn: Txn, ino: Ino, i: MemInode)
      modifies fs.Repr, i.Repr
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i)
      ensures Valid()
      ensures data() == old(data())
      ensures types_unchanged()
    {
      fs.finishInode(txn, ino, i);
      assert types_unchanged() by {
        reveal inode_types();
      }
    }

    ghost method finishInodeReadonly(ino: Ino, i: MemInode)
      modifies fs.fs
      requires fs.ValidIno(ino, i)
      requires fs.fs.cur_inode == Some((ino, i.val()))
      ensures Valid()
      ensures data() == old(data())
      ensures types_unchanged()
    {
      fs.finishInodeReadonly(ino, i);
      assert types_unchanged() by {
        reveal inode_types();
      }
    }

  }
}
