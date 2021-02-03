include "fs.dfy"
include "../../util/min_max.dfy"

module ByteFs {
  import opened Fs
  import opened FsKinds
  import opened JrnlSpec
  import opened Machine
  import opened ByteSlice
  import opened MinMax
  import C = Collections

  function {:opaque} inode_data(d: InodeData): (bs:seq<byte>)
    requires forall i:nat | i < |d.blks| :: is_block(d.blks[i])
    requires |d.blks| == Round.div_roundup_alt(d.sz, 4096)
    ensures |bs| == d.sz
  {
    C.concat_homogeneous_spec(d.blks, 4096);
    C.concat(d.blks)[..d.sz]
  }

  lemma inode_data_aligned(d: InodeData)
    requires d.sz % 4096 == 0
    requires forall i:nat | i < |d.blks| :: is_block(d.blks[i])
    requires |d.blks| == Round.div_roundup_alt(d.sz, 4096)
    ensures inode_data(d) == C.concat(d.blks)
  {
    reveal_inode_data();
    C.concat_homogeneous_len(d.blks, 4096);
  }

  class ByteFilesys {
    ghost var data: map<Ino, seq<byte>>;

    const fs: Filesys;

    function Repr(): set<object>
    {
      {this} + fs.Repr()
    }

    static predicate inode_blks_to_data(inode_blks: map<Ino, InodeData>, data: map<Ino, seq<byte>>)
    {
      && ino_dom(inode_blks)
      && ino_dom(data)
      && Valid_inode_blks(inode_blks)
      && (forall ino | ino_ok(ino) :: data[ino] == inode_data(inode_blks[ino]))
    }

    predicate Valid()
      reads this.Repr()
    {
      && fs.Valid()
      && inode_blks_to_data(fs.inode_blks, data)
    }

    constructor Init(d: Disk)
      ensures Valid()
    {
      fs := new Filesys.Init(d);
      data := map ino | ino_ok(ino) :: [];
    }

    method Get(ino: Ino, off: uint64, len: uint64)
      returns (bs: Bytes, ok: bool)
      modifies {}
      requires ino_ok(ino)
      requires Valid() ensures Valid()
      ensures fresh(bs) && bs.Valid()
      ensures ok ==>
      && off as nat + len as nat <= |data[ino]|
      && bs.data == data[ino][off..off+len]
    {
      if len > 4096 {
        ok := false;
        bs := NewBytes(0);
        return;
      }

      var txn := fs.jrnl.Begin();
      var i := fs.getInode(txn, ino);
      if sum_overflows(off, len) || off+len > i.sz {
        ok := false;
        bs := NewBytes(0);
        return;
      }

      ok := true;
      if len == 0 {
        bs := NewBytes(0);
        return;
      }
      assert 0 < len <= 4096;

      var blkoff: nat := off as nat / 4096;
      ghost var off': nat := blkoff * 4096;
      Arith.div_mod_split(off as nat, 4096);

      bs := fs.getInodeBlk(txn, ino, i, blkoff);

      ghost var blks := fs.inode_blks[ino].blks;
      assert off' + 4096 <= |C.concat(blks)| &&
        bs.data == C.concat(blks)[off'..off'+4096] by {
        C.concat_homogeneous_one_list(blks, blkoff, 4096);
        reveal_inode_data();
      }

      if off % 4096 + len <= 4096 {
        // we finished the entire read
        bs.Subslice(off % 4096, off % 4096 + len);

        C.double_subslice(C.concat(blks),
          off', off'+4096,
          off as nat % 4096, off as nat % 4096 + len as nat);

        var _ := txn.Commit();
        reveal_inode_data();
        return;
      }

      bs.Subslice(off % 4096, 4096);
      var read_bytes: uint64 := bs.Len();
      assert bs.data == data[ino][off..off + read_bytes] by {
        C.double_subslice(C.concat(blks),
          off', off'+4096,
          off as nat % 4096, 4096);
          reveal_inode_data();
      }

      var bs2 := fs.getInodeBlk(txn, ino, i, blkoff+1);
      assert off'+8192 <= |C.concat(blks)| &&
        bs2.data == C.concat(blks)[off'+4096..off'+8192] by {
        C.concat_homogeneous_one_list(blks, blkoff+1, 4096);
      }
      bs2.Subslice(0, len - read_bytes);
      assert bs2.data == data[ino][off + read_bytes..off + len] by {
        reveal_inode_data();
      }

      bs.AppendBytes(bs2);
      assert bs.data == data[ino][off..off + len];

      var _ := txn.Commit();
    }

    method Size(ino: Ino) returns (sz: uint64)
      modifies {}
      requires Valid() ensures Valid()
      requires ino_ok(ino)
      ensures sz as nat == |data[ino]|
    {
      sz := fs.Size(ino);
    }

    function get_last_block(d: InodeData): Block
      requires 0 < |d.blks|
    {
      C.last(d.blks)
    }

    function set_last_block(d: InodeData, b: Block): InodeData
      requires 0 < |d.blks|
    {
      var blks := d.blks;
      var off := |d.blks|-1;
      d.(blks:=blks[off := b])
    }

    lemma inode_data_splice_last(d: InodeData, d': InodeData, bs: seq<byte>)
      requires 0 < |d.blks|
      requires d.sz % 4096 + |bs| <= 4096
      requires InodeData_Valid(d)
      requires InodeData_Valid(d')
      requires (assert is_block(get_last_block(d));
                d' == set_last_block(d, C.splice(get_last_block(d), d.sz % 4096, bs)).(sz:=d.sz + |bs|))
      ensures inode_data(d') == inode_data(d) + bs
    {
      reveal_inode_data();
      C.concat_split_last(d.blks);
      C.concat_homogeneous_len(d.blks, 4096);
      C.concat_split_last(d'.blks);
      C.concat_homogeneous_len(C.without_last(d'.blks), 4096);
      calc {
        inode_data(d');
        (C.concat(C.without_last(d'.blks)) + C.last(d'.blks))[..d'.sz];
        C.concat(C.without_last(d'.blks)) + C.last(d'.blks)[..d'.sz - (|d'.blks|-1) * 4096];
        C.concat(C.without_last(d.blks)) + C.last(d'.blks)[..d'.sz - (|d'.blks|-1) * 4096];
      }
    }

    lemma inode_data_replace_last(d: InodeData, d': InodeData, bs: seq<byte>, new_bytes: nat)
      requires 0 < |d.blks|
      requires d.sz % 4096 == 0 && |bs| == 4096
      requires InodeData_Valid(d)
      requires InodeData_Valid(d')
      requires (assert is_block(get_last_block(d));
                d' == set_last_block(d, bs).(sz:=d.sz - 4096 + new_bytes))
      ensures inode_data(d') == inode_data(d)[..d.sz - 4096] + bs[..new_bytes]
    {
      reveal_inode_data();
      C.concat_split_last(d.blks);
      C.concat_homogeneous_len(d.blks, 4096);
      C.concat_split_last(d'.blks);
      assert C.concat(C.without_last(d.blks)) == inode_data(d)[..d.sz - 4096];
    }

    method writeLastBlock(txn: Txn, ino: Ino, i: Inode.Inode, bn: Blkno, bs: Bytes)
      modifies Repr()
      requires Valid() ensures Valid()
      requires txn.jrnl == fs.jrnl
      requires fs.is_inode(ino, i)
      requires 0 < |i.blks|
      requires i.blks[|i.blks|-1] == bn
      requires i.sz % 4096 == 0
      requires 4096 <= i.sz
      requires bs.Valid()
      requires 0 < bs.Len() <= 4096
      ensures (var d := old(data[ino]);
            data == old(data[ino:= d[..|d|-4096] + bs.data]))
    {
        var blk := NewBytes(4096);
        blk.CopyTo(0, bs);
        fs.writeDataBlock(txn, bn, blk, ino, |i.blks|-1);
        var i'' := i.(sz:=i.sz - 4096 + bs.Len());
        // this truncates the inode, which growInode grows for the sake of
        // preserving the complete inode invariant
        fs.writeInodeSz(txn, ino, i, i'');
        assert fs.Valid() by {
          Filesys.reveal_Valid_inodes_to_block_used();
        }

        ghost var ino_d := data[ino];
        ghost var stable_d := ino_d[..|ino_d|-4096];
        data := data[ino:= stable_d + bs.data];

        ghost var d' := fs.inode_blks[ino];
        assert inode_data(d') == stable_d + bs.data by {
          inode_data_replace_last(old(fs.inode_blks[ino]), fs.inode_blks[ino], blk.data, |bs.data|);
          assert blk.data[..|bs.data|] == bs.data;
        }
    }

    method appendAligned(txn: Txn, ino: Ino, i: Inode.Inode, bs: Bytes) returns (ok:bool)
      modifies Repr()
      requires Valid() ensures Valid()
      requires txn.jrnl == fs.jrnl
      requires fs.is_inode(ino, i)
      requires i.sz % 4096 == 0
      requires bs.Valid()
      requires 0 < bs.Len() <= 4096
      requires i.sz as nat + |bs.data| <= 15*4096
      ensures ok ==> data == old(data[ino:=data[ino] + bs.data])
      ensures !ok ==> data == old(data)
    {
      // add some garbage data to the end of the inode
      var alloc_ok, bn := fs.growInode(txn, ino, i);
      if !alloc_ok {
        ok := false;
        return;
      }
      data := data[ino:=data[ino] + fs.data_block[bn]];
      assert Valid() by {
        C.concat_app1(old(fs.inode_blks[ino].blks), fs.data_block[bn]);
        inode_data_aligned(old(fs.inode_blks[ino]));
        inode_data_aligned(fs.inode_blks[ino]);
      }
      ok := true;

      label post_grow:
        // avoid unused label in Go
        //
        // see https://github.com/dafny-lang/dafny/issues/1093
      { break post_grow; }

      assert data[ino][..old(fs.inode_blks[ino].sz)] == old(data[ino]);

      var i' := Filesys.inode_append(i, bn);
      assert fs.is_inode(ino, i');

      if bs.Len() < 4096 {

        writeLastBlock(txn, ino, i', bn, bs);
        return;

      } else {

        assert |bs.data| == 4096;
        fs.writeDataBlock(txn, bn, bs, ino, |i'.blks|-1);
        assert fs.Valid();

        assert i'.sz == i.sz + bs.Len();
        data := data[ino:=old(data[ino]) + bs.data];

        ghost var d' := fs.inode_blks[ino];
        assert inode_data(d') == old(data[ino]) + bs.data by {
          inode_data_replace_last(old@post_grow(fs.inode_blks[ino]), d', bs.data, |bs.data|);
          assert bs.data[..|bs.data|] == bs.data;
        }
        assert Valid();
        return;

      }
      assert false;
    }

    method appendAtEnd(txn: Txn, ino: Ino, i: Inode.Inode, bs: Bytes) returns (i': Inode.Inode, ghost written: nat, bs': Bytes)
      modifies Repr(), bs
      requires txn.jrnl == fs.jrnl
      requires Valid() ensures Valid()
      requires fs.is_inode(ino, i)
      requires bs.Valid()
      requires |data[ino]| + |bs.data| < 15*4096
      requires 0 < |bs.data| <= 4096
      ensures written <= old(|bs.data|)
      ensures bs'.Valid()
      ensures bs'.Len() == 0 ==> written == old(|bs.data|)
      ensures bs'.Len() != 0 ==> i'.sz % 4096 == 0 && written < old(|bs.data|)
      ensures data == old(data[ino:=data[ino] + bs.data[..written]])
      // bs' reports the remainder to be written
      ensures bs'.data == old(bs.data[written..])
      ensures fs.is_inode(ino, i')
    {
      var remaining_space := Round.roundup64(i.sz, 4096) - i.sz;
      if remaining_space == 0 {
        // sz is already aligned
        written := 0;
        i' := i;
        bs' := bs;
        assert data[ino] + bs.data[..written] == data[ino];
        return;
      }

      assert remaining_space == 4096 - i.sz % 4096;
      var to_write: uint64 := min_u64(remaining_space, bs.Len());
      written := to_write as nat;
      bs' := bs.Split(to_write);
      Round.roundup_distance(i.sz as nat, 4096);
      fs.inode_blks_sz(ino);
      var blkoff: nat := i.sz as nat/4096;
      assert blkoff == |i.blks|-1;
      var blk := fs.getInodeBlk(txn, ino, i, blkoff);
      assert |bs.data| <= |old(bs.data)|;
      assert |bs.data| <= remaining_space as nat;
      blk.CopyTo(i.sz % 4096, bs);
      var bn := i.blks[blkoff];
      fs.writeDataBlock(txn, bn, blk, ino, blkoff);

      i' := i.(sz := i.sz + bs.Len());
      assert Inode.Valid(i');
      fs.writeInodeSz(txn, ino, i, i');

      assert fs.Valid() by {
        Filesys.reveal_Valid_inodes_to_block_used();
      }

      data := data[ino := data[ino] + bs.data];
      assert Valid() by {
        assert fs.is_inode(ino, i');
        inode_data_splice_last(old(fs.inode_blks[ino]), fs.inode_blks[ino], bs.data);
      }
    }

    method Append(ino: Ino, bs: Bytes) returns (ok:bool)
      modifies Repr(), bs
      requires Valid() ensures Valid()
      requires ino_ok(ino)
      requires bs.Valid()
      requires bs.Len() <= 4096
      ensures ok ==> data == old(data[ino:=data[ino] + bs.data])
      // FIXME: not true because we do some writes before aborting;
      // we probably shouldn't do this in Dafny at all
      // ensures !ok ==> data == old(data)
    {
      var txn := fs.jrnl.Begin();

      // check for available space
      var i := fs.getInode(txn, ino);
      fs.inode_sz_no_overflow(ino, i, bs.Len());
      if  i.sz + bs.Len() >= 15*4096 {
        ok := false;
        return;
      }
      if bs.Len() == 0 {
        ok := true;
        assert bs.data == [];
        assert data[ino] == data[ino] + bs.data;
        return;
      }

      ghost var written;
      var bs';
      i, written, bs' := appendAtEnd(txn, ino, i, bs);
      if bs'.Len() == 0 {
        ok := true;
        var _ := txn.Commit();
        assert old(bs.data[..written]) == old(bs.data);
        return;
      }
      assert i.sz % 4096 == 0;
      assert fs.is_inode(ino, i);

      // we still need to write bs'
      assert data[ino] + bs'.data == old(data[ino] + bs.data);

      // TODO: this can abort after preparing the transaction; do we want to support that?
      ok := appendAligned(txn, ino, i, bs');
      if !ok {
        return;
      }
      var _ := txn.Commit();
    }
  }
}
