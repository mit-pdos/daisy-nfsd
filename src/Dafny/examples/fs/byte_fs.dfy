include "fs.dfy"

module ByteFs {
  import opened Fs
  import opened FsKinds
  import opened JrnlSpec
  import opened Machine
  import opened ByteSlice

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

    method Append(ino: Ino, bs: Bytes) returns (ok:bool)
      modifies this, fs.Repr()
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

      // is there space in the last block?
      if i.sz + bs.Len() <= Round.roundup64(i.sz, 4096) {
        Round.roundup_distance(i.sz as nat, 4096);

        fs.inode_blks_sz(ino);
        var blkoff: nat := i.sz as nat/4096;
        assert blkoff == |i.blks|-1;
        var blk := fs.getInodeBlk(txn, ino, i, blkoff);
        blk.CopyTo(i.sz % 4096, bs);
        var bn := i.blks[blkoff];
        fs.writeDataBlock(txn, bn, blk, ino, blkoff);

        var i' := i.(sz := i.sz + bs.Len());
        assert Inode.Valid(i');
        fs.writeInodeSz(txn, ino, i, i');

        assert fs.Valid() by {
          Filesys.reveal_Valid_inodes_to_block_used();
        }

        ghost var sz := i.sz as nat;
        ghost var sz' := i'.sz as nat;
        data := data[ino := data[ino] + bs.data];
        ghost var i_blks: seq<Block> := old(fs.inode_blks[ino].blks);
        ghost var i_blks': seq<Block> := fs.inode_blks[ino].blks;
        ghost var i_data := old(data[ino]);
        ghost var i_data' := data[ino];

        // TODO: this much calc is a little excessive but I'm scared to reduce it

        C.concat_split_last(i_blks);
        C.concat_homogeneous_len(i_blks, 4096);
        calc {
          i_data;
          inode_data(InodeData(sz, i_blks));
          C.concat(i_blks)[..sz];
          (C.concat(C.without_last(i_blks)) + C.last(i_blks))[..sz];
          C.concat(C.without_last(i_blks)) + C.last(i_blks)[..sz % 4096];
          C.concat(C.without_last(i_blks)) + blk.data[..sz % 4096];
        }

        C.concat_split_last(i_blks');
        C.concat_homogeneous_len(C.without_last(i_blks'), 4096);
        calc {
          i_data';
          (C.concat(C.without_last(i_blks')) + C.last(i_blks'))[..sz'];
          C.concat(C.without_last(i_blks)) + C.last(i_blks)[..sz % 4096] + bs.data;
          inode_data(InodeData(sz', i_blks'));
        }

        ok := true;
        return;
      }

      if i.sz % 4096 != 0 {
        // TODO: need to handle this by first doing a partial write to the last
        // block
        ok := false;
        return;
      }

      // add some garbage data to the end of the inode
      var alloc_ok, bn := fs.growInode(txn, ino, i);
      if !alloc_ok {
        ok := false;
        return;
      }

      var i' := Filesys.inode_append(i, bn);
      var blk := NewBytes(4096);
      blk.CopyTo(0, bs);
      fs.writeDataBlock(txn, bn, blk, ino, |i'.blks|-1);
      if bs.Len() < 4096 {
        var i'' := i'.(sz:=i.sz + bs.Len());
        // this truncates the inode, which growInode grows for the sake of
        // preserving the complete inode invariant
        fs.writeInodeSz(txn, ino, i', i'');
        assert fs.Valid() by {
          Filesys.reveal_Valid_inodes_to_block_used();
        }
      }
      assert fs.Valid();

      assume false;

      ok := true;
      var _ := txn.Commit();
    }
  }
}
