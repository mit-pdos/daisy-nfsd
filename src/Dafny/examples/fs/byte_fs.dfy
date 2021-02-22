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

  class ByteFilesys<InodeAllocState(!new)>
  {
    const fs: IndFilesys<InodeAllocState>;
    const Repr: set<object> := fs.Repr

    predicate Valid()
      reads this.Repr
    {
      && fs.ValidQ()
    }

    function data(): map<Ino, seq<byte>>
      reads Repr
      requires fs.Valid()
    {
      map ino:Ino | ino_ok(ino) ::
        (fs.metadata_bound(ino);
        inode_data(fs.metadata[ino].sz as nat, block_data(fs.data)[ino]))
    }

    function {:opaque} inode_types(): (m:map<Ino, Inode.InodeType>)
      reads fs.Repr
      requires fs.Valid()
      ensures Fs.ino_dom(m)
    {
      map ino: Ino | ino_ok(ino) :: fs.metadata[ino].ty
    }

    twostate predicate types_unchanged()
      reads fs.Repr
      requires old(fs.Valid()) && fs.Valid()
    {
      inode_types() == old(inode_types())
    }

    twostate lemma inode_types_metadata_unchanged()
      requires old(fs.Valid()) && fs.Valid()
      requires fs.metadata == old(fs.metadata)
      ensures types_unchanged()
    {
      reveal inode_types();
    }

    function raw_data(ino: Ino): seq<byte>
      reads Repr
      requires ino_ok(ino)
      requires fs.Valid()
    {
      raw_inode_data(block_data(fs.data)[ino])
    }

    constructor Init(d: Disk)
      ensures Valid()
      ensures data() == map ino: Ino | ino_ok(ino) :: []
      ensures inode_types() == map ino: Ino | ino_ok(ino) :: Inode.FileType
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
    method {:timeLimitMultiplier 2} read_txn(txn: Txn, ino: Ino, off: uint64, len: uint64)
      returns (bs: Bytes, ok: bool)
      modifies fs.fs
      requires fs.has_jrnl(txn)
      requires Valid() ensures Valid()
      requires ino_ok(ino)
      ensures fs.inode_owner() == old(fs.inode_owner())
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

    // public
    method Read(ino: Ino, off: uint64, len: uint64)
      returns (bs: Bytes, ok: bool)
      modifies fs.fs
      requires Valid() ensures Valid()
      requires ino_ok(ino)
      ensures ok ==>
          && off as nat + len as nat <= |data()[ino]|
          && bs.data == this.data()[ino][off..off+len]
      ensures data() == old(data())
    {
      var txn := fs.fs.jrnl.Begin();
      bs, ok := read_txn(txn, ino, off, len);
      // TODO: this is read-only, no need to commit the transaction
      var _ := txn.Commit();
    }

    // public
    //
    // this variant can be used in a larger transaction
    method size_txn(txn: Txn, ino: Ino) returns (sz: uint64)
      modifies fs.fs
      requires fs.has_jrnl(txn)
      requires Valid() ensures Valid()
      requires ino_ok(ino)
      ensures data() == old(data())
      ensures sz as nat == |data()[ino]|
    {
      var i := fs.startInode(txn, ino);
      sz := i.sz;
      fs.inode_metadata(ino, i);
      fs.finishInodeReadonly(ino, i);
      var _ := txn.Commit();
    }

    // public
    method Size(ino: Ino) returns (sz: uint64)
      modifies fs.fs
      requires Valid() ensures Valid()
      requires ino_ok(ino)
      ensures data() == old(data())
      ensures sz as nat == |data()[ino]|
    {
      var txn := fs.fs.jrnl.Begin();
      sz := size_txn(txn, ino);
      // TODO: this is read-only, no need to commit the transaction
      var _ := txn.Commit();
    }

    // private
    method alignedRawWrite(txn: Txn, ino: Ino, i: Inode.Inode, bs: Bytes, off: uint64)
      returns (ok: bool, i': Inode.Inode)
      modifies Repr
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
      ensures fs.inode_owner() == old(fs.inode_owner())
      ensures types_unchanged()
      ensures !ok ==> raw_data(ino) == old(raw_data(ino))
      ensures !ok ==> data() == old(data())
    {
      i' := i;
      var blkoff: nat := off as nat / 4096;
      var wh := new BlockFs.WriteHelper(fs);
      ok, i' := wh.Do(txn, ino, i, blkoff as nat, bs);
      assert types_unchanged() by {
        reveal inode_types();
      }
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
      inode_types_metadata_unchanged();
    }

    // private
    method alignedWrite(txn: Txn, ino: Ino, i: Inode.Inode, bs: Bytes, off: uint64)
      returns (ok: bool, i': Inode.Inode)
      modifies Repr
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i')
      requires is_block(bs.data)
      requires off % 4096 == 0
      requires off as nat + 4096 <= |data()[ino]|
      ensures bs.data == old(bs.data)
      ensures fs.metadata == old(fs.metadata);
      ensures fs.inode_owner() == old(fs.inode_owner())
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
    method growBy(ghost ino: Ino, i: Inode.Inode, delta: uint64)
      returns (i': Inode.Inode, ghost junk: seq<byte>)
      modifies Repr
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i')
      requires i.sz as nat + delta as nat <= Inode.MAX_SZ
      ensures |junk| == delta as nat
      ensures data() == old(data()[ino := data()[ino] + junk])
      ensures fs.inode_owner() == old(fs.inode_owner())
      ensures types_unchanged()
    {
      fs.inode_metadata(ino, i);
      ghost var sz := i.sz;
      var sz' := i.sz + delta;
      i' := fs.writeInodeMeta(ino, i, i.meta.(sz := sz'));
      fs.inode_metadata(ino, i');
      assert raw_data(ino) == old(raw_data(ino));
      junk := raw_data(ino)[sz..sz'];
      assert data()[ino] == old(data()[ino] + junk) by {
        reveal raw_inode_data();
      }
      assert types_unchanged() by {
        reveal inode_types();
      }
    }

    method shrinkTo(ghost ino: Ino, i: Inode.Inode, sz': uint64)
      returns (i': Inode.Inode)
      modifies Repr
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i')
      requires sz' <= i.sz
      ensures sz' as nat <= old(|data()[ino]|)
      ensures data() == old(data()[ino := data()[ino][..sz' as nat]])
      ensures fs.inode_owner() == old(fs.inode_owner())
      ensures types_unchanged()
    {
      fs.inode_metadata(ino, i);
      i' := fs.writeInodeMeta(ino, i, i.meta.(sz:=sz'));
      fs.inode_metadata(ino, i');
      assert raw_data(ino) == old(raw_data(ino));
      assert data()[ino] == old(data()[ino][..sz' as nat]) by {
        reveal raw_inode_data();
      }
      assert types_unchanged() by {
        reveal inode_types();
      }
    }

    lemma data_update_in_place(data0: seq<byte>, data1: seq<byte>, off: nat, bs: seq<byte>, blk: seq<byte>)
      requires off as nat + |bs| <= off/4096*4096 + 4096 <= |data0|
      requires
      (var off' := off / 4096 * 4096;
      && blk == C.splice(data0[off'..off'+4096], off % 4096, bs)
      && data1 == C.splice(data0, off', blk)
      )
      ensures data1 == C.splice(data0, off, bs)
    {
      var off' := off / 4096 * 4096;
      assert data1 == C.splice(data0, off', blk);
      forall i: nat | i < |data0|
        ensures C.splice(data0, off', blk)[i] == C.splice(data0, off, bs)[i]
      {
        C.splice_get_i(data0, off, bs, i);
        C.splice_get_i(data0, off', blk, i);
        if 0 <= i - off' < 4096 {
          C.splice_get_i(blk, off % 4096, bs, i - off');
        }
      }
      assert data1 == C.splice(data0, off, bs);
    }

    // private
    method {:timeLimitMultiplier 2} updateInPlace(txn: Txn, ino: Ino, i: Inode.Inode, off: uint64, bs: Bytes)
      returns (ok: bool, i': Inode.Inode)
      modifies Repr
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i')
      requires off as nat + |bs.data| <= off as nat/4096*4096 + 4096 <= |data()[ino]|
      ensures fs.inode_owner() == old(fs.inode_owner())
      ensures types_unchanged()
      ensures ok ==>
        data() == old(
        var d := data()[ino];
        var d' := C.splice(d, off as nat, bs.data);
        data()[ino := d'])
    {
      i' := i;
      if off % 4096 == 0 && bs.Len() == 4096 {
        ok, i' := this.alignedWrite(txn, ino, i', bs, off);
        inode_types_metadata_unchanged();
        return;
      }
      ghost var data0 := data()[ino];

      var off_u64 := off;
      var aligned_off: uint64 := off_u64 / 4096 * 4096;
      ghost var off: nat := off_u64 as nat;
      ghost var off': nat := off / 4096 * 4096;

      //Round.roundup_distance(off as nat, 4096);
      var blk := this.alignedRead(txn, ino, i', aligned_off);

      assert blk.data == data0[off'..off'+4096];

      blk.CopyTo(off_u64 % 4096, bs);
      ok, i' := this.alignedWrite(txn, ino, i', blk, aligned_off);
      if !ok {
        inode_types_metadata_unchanged();
        return;
      }
      ghost var data1 := data()[ino];
      assert fs.ValidIno(ino, i');
      assert |data1| == |data0|;
      //assert off' == aligned_off as nat;
      //assert off == off_u64 as nat;
      //assert off == off' + off % 4096;

      assert data1 == C.splice(data0, off, bs.data) by {
        //assert (off_u64 % 4096) as nat == off % 4096;
        data_update_in_place(data0, data1, off, bs.data, blk.data);
      }
      inode_types_metadata_unchanged();
    }

    // private
    method {:timeLimitMultiplier 2} appendAtEnd(txn: Txn, ino: Ino, i: Inode.Inode, bs: Bytes)
      returns (ok: bool, i': Inode.Inode, ghost written: nat, bs': Bytes)
      modifies Repr, bs
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i')
      requires bs.Valid()
      requires i.sz as nat + |bs.data| <= Inode.MAX_SZ
      requires 0 < |bs.data| <= 4096
      ensures written <= old(|bs.data|)
      // we don't make this abstract because it's needed to guarantee progress
      ensures written == old(min(4096 - |data()[ino]| % 4096, |bs.data|))
      ensures ok ==> fresh(bs') && bs'.Valid() && bs'.data == old(bs.data[written..])
      ensures ok ==> data() == old(data()[ino := data()[ino] + bs.data[..written]])
      ensures !ok ==> data == old(data)
      ensures fs.inode_owner() == old(fs.inode_owner())
      ensures types_unchanged()
    {
      i' := i;
      fs.inode_metadata(ino, i');

      var remaining_space := 4096 - i.sz % 4096;
      ghost var data0 := data()[ino];
      ghost var junk;
      i', junk := this.growBy(ino, i', remaining_space);
      ghost var data1 := data()[ino];
      assert data1 == data0 + junk;

      var to_write: uint64 := min_u64(remaining_space, bs.Len());
      var desired_size: uint64 := i.sz + to_write;
      assert desired_size as nat <= i.sz as nat + remaining_space as nat;
      written := to_write as nat;

      bs' := bs.Split(to_write);
      assert bs.data == old(bs.data[..written]);
      Round.roundup_distance(i.sz as nat, 4096);
      ok, i' := this.updateInPlace(txn, ino, i', i.sz, bs);
      if !ok {
        return;
      }
      if bs'.Len() == 0 {
        assert written == old(|bs.data|);
        assert old(bs.data[..written]) == old(bs.data);
      }
      fs.inode_metadata(ino, i');
      ghost var data2 := data()[ino];
      assert desired_size as nat == i.sz as nat + to_write as nat;

      i' := shrinkTo(ino, i', desired_size);
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

    method alignedAppend(txn: Txn, ino: Ino, i: Inode.Inode, bs: Bytes)
      returns (ok: bool, i': Inode.Inode)
      modifies Repr, bs
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i')
      requires bs.Valid()
      requires i.sz as nat + |bs.data| <= Inode.MAX_SZ
      requires 0 < |bs.data| <= 4096
      requires |data()[ino]| % 4096 == 0
      ensures ok ==> data() == old(data()[ino := data()[ino] + bs.data])
      ensures !ok ==> data == old(data)
      ensures fs.inode_owner() == old(fs.inode_owner())
      ensures types_unchanged()
    {
      ghost var written;
      var bs';
      ok, i', written, bs' := appendAtEnd(txn, ino, i, bs);
      assert written == old(|bs.data|);
      assert old(bs.data[..written]) == old(bs.data);
    }

    method {:timeLimitMultiplier 2} appendIno(txn: Txn, ino: Ino, i: Inode.Inode, bs: Bytes)
      returns (ok:bool, i': Inode.Inode)
      modifies Repr, bs
      requires fs.has_jrnl(txn)
      requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i')
      requires bs.Valid() && 0 < bs.Len() <= 4096
      requires |data()[ino]| + |bs.data| <= Inode.MAX_SZ
      ensures ok ==> data() == old(data()[ino := data()[ino] + bs.data])
      ensures fs.inode_owner() == old(fs.inode_owner())
      ensures types_unchanged()
    {
      i' := i;
      fs.inode_metadata(ino, i');
      ghost var sz0 := i.sz as nat;

      ghost var written;
      var bs';
      ok, i', written, bs' := this.appendAtEnd(txn, ino, i', bs);
      assert types_unchanged();
      if !ok {
        // TODO: we should really just abort here
        return;
      }
      if bs'.Len() == 0 {
        assert old(bs.data[..written]) == old(bs.data);
        return;
      }
      fs.inode_metadata(ino, i');
      assert i'.sz as nat + |bs'.data| == sz0 + old(|bs.data|) by {
        assert old(|bs.data[..written]|) == written;
        assert |bs'.data| == old(|bs.data|) - written;
        assert |data()[ino]| == old(|data()[ino]|) + written;
      }
      assert |data()[ino]| % 4096 == 0;

      ok, i' := this.alignedAppend(txn, ino, i', bs');
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

    // public
    //
    // this variant can be used in a larger transaction
    method append_txn(txn: Txn, ino: Ino, bs: Bytes)
      returns (ok:bool)
      modifies Repr, bs
      requires fs.has_jrnl(txn)
      requires Valid() ensures Valid()
      requires ino_ok(ino)
      requires bs.Valid()
      requires bs.Len() <= 4096
      ensures ok ==> data() == old(data()[ino := data()[ino] + bs.data])
      ensures fs.inode_owner() == old(fs.inode_owner())
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
      ok, i := this.appendIno(txn, ino, i, bs);
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
      requires ino_ok(ino)
      requires bs.Valid()
      requires bs.Len() <= 4096
      ensures ok ==> data() == old(data()[ino := data()[ino] + bs.data])
    {
      var txn := fs.fs.jrnl.Begin();
      ok := append_txn(txn, ino, bs);
      if !ok {
        // abort
        return;
      }
      ok := txn.Commit();
    }

  }
}
