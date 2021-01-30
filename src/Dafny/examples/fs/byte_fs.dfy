include "fs.dfy"

module ByteFs {
  import opened Fs
  import opened FsKinds
  import opened JrnlSpec
  import opened Machine
  import opened ByteSlice

  // TODO: implement this on top of the lower-level API in fs.dfy

  function inode_data_alt(d: InodeData): (bs:seq<byte>)
    requires forall i:nat | i < |d.blks| :: is_block(d.blks[i])
    requires |d.blks| == Round.div_roundup_alt(d.sz, 4096)
    ensures |bs| == d.sz
  {
    var blks := d.blks;
    if d.sz % 4096 == 0 then (
      C.concat_homogeneous_spec(blks, 4096);
      C.concat(blks)
      )
    else (
      C.concat_homogeneous_spec(C.without_last(blks), 4096);
      C.concat(C.without_last(blks)) +
      C.last(blks)[..d.sz % 4096]
      )
  }

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
    {
      ok := fs.Append(ino, bs);
      data := data[ino := data[ino] + bs.data];
      assume false;
    }
  }
}
