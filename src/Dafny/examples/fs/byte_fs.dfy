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

  function inode_data(d: InodeData): (bs:seq<byte>)
    requires forall i:nat | i < |d.blks| :: is_block(d.blks[i])
    requires |d.blks| == Round.div_roundup_alt(d.sz, 4096)
    ensures |bs| == d.sz
  {
    C.concat_homogeneous_spec(d.blks, 4096);
    C.concat(d.blks)[..d.sz]
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
      requires off % 4096 == 0 && len <= 4096
      requires ino_ok(ino)
      requires Valid() ensures Valid()
      ensures ok ==>
      && off as nat + len as nat <= |data[ino]|
      && bs.data == data[ino][off..off+len]
    {
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
      bs := fs.getInodeBlk(txn, ino, i, blkoff);
      C.concat_homogeneous_one_list(fs.inode_blks[ino].blks, blkoff, 4096);
      bs.Subslice(0, len);
      assert blkoff * 4096 == off as nat;

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

    method Append(ino: Ino, bs: Bytes) returns (ok:bool)
      modifies Repr(), bs
      requires Valid() ensures Valid()
      requires ino_ok(ino)
      requires bs.Valid()
      requires bs.Len() <= 4096
      ensures ok ==> data == old(data)[ino:=old(data[ino]) + bs.data]
    {
      var txn := fs.jrnl.Begin();

      // check for available space
      var i := fs.getInode(txn, ino);
      if sum_overflows(i.sz, bs.Len()) || i.sz + bs.Len() >= 15*4096 {
        ok := false;
        return;
      }
      if bs.Len() == 0 {
        ok := true;
        assert bs.data == [];
        assert data[ino] == data[ino] + bs.data;
        return;
      }
      assert fs.is_inode(ino, i);

      var remaining_space := Round.roundup64(i.sz, 4096) - i.sz;

      var bs' := bs;
      if remaining_space > 0 {
        assert remaining_space == 4096 - i.sz % 4096;
        bs' := bs.Split(min_u64(remaining_space, bs.Len()));
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

        var i' := i.(sz := i.sz + bs.Len());
        assert Inode.Valid(i');
        fs.writeInodeSz(txn, ino, i, i');

        assert fs.Valid() by {
          Filesys.reveal_Valid_inodes_to_block_used();
        }

        data := data[ino := data[ino] + bs.data];
        inode_data_splice_last(old(fs.inode_blks[ino]), fs.inode_blks[ino], bs.data);

        assert old(bs.data) == bs.data + bs'.data;
        assert 0 < |bs'.data| ==> fs.inode_blks[ino].sz % 4096 == 0;

        // fix up the inode for the rest of the function
        //
        // NOTE: this was caught by verification (due to the precondition of
        // fs.growInode() specifically)
        i := i';
        assert fs.is_inode(ino, i);
      }
      //label post_fixup:
      // we still need to write bs'

      if bs'.Len() == 0 {
        ok := true;
        return;
      }

      // if we had any remaining space from this being non-zero, we have no
      // written to it
      assert fs.inode_blks[ino].sz % 4096 == 0;

      // add some garbage data to the end of the inode
      var alloc_ok, bn := fs.growInode(txn, ino, i);
      if !alloc_ok {
        ok := false;
        return;
      }
      //label post_grow:

      var i' := Filesys.inode_append(i, bn);
      assert fs.is_inode(ino, i');

      if bs'.Len() < 4096 {
        var blk := NewBytes(4096);
        blk.CopyTo(0, bs');
        fs.writeDataBlock(txn, bn, blk, ino, |i'.blks|-1);
        var i'' := i'.(sz:=i.sz + bs'.Len());
        // this truncates the inode, which growInode grows for the sake of
        // preserving the complete inode invariant
        fs.writeInodeSz(txn, ino, i', i'');
        assert fs.Valid() by {
          Filesys.reveal_Valid_inodes_to_block_used();
        }

        data := data[ino:=data[ino] + bs'.data];

      } else {
        assert |bs'.data| == 4096;
        fs.writeDataBlock(txn, bn, bs', ino, |i'.blks|-1);
        assert fs.Valid();

        assert i'.sz == i.sz + bs'.Len();
        data := data[ino:=data[ino] + bs'.data];

      }

      assume false;

      ok := true;
      var _ := txn.Commit();
    }
  }
}
