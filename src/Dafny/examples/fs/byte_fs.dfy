include "fs.dfy"
include "../../util/min_max.dfy"

module ByteFs {
  import opened Fs
  import opened FsKinds
  import opened JrnlSpec
  import opened Machine
  import opened ByteSlice
  import opened MinMax

  function {:opaque} inode_data(d: InodeData): (bs:seq<byte>)
    requires d.Valid()
    ensures |bs| == d.sz
  {
    d.used_blocks_valid();
    C.concat_homogeneous_spec(d.used_blocks(), 4096);
    C.concat(d.used_blocks())[..d.sz]
  }

  lemma inode_data_aligned(d: InodeData)
    requires d.sz % 4096 == 0
    requires d.Valid()
    ensures inode_data(d) == C.concat(d.used_blocks())
  {
    reveal_inode_data();
    d.used_blocks_valid();
    C.concat_homogeneous_len(d.used_blocks(), 4096);
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
      && fs.ValidQ()
      && inode_blks_to_data(fs.inode_blks, data)
    }

    predicate ValidIno(ino: Ino, i: Inode.Inode)
      reads this.Repr()
    {
      && fs.Valid()
      && fs.is_cur_inode(ino, i)
      && inode_blks_to_data(fs.inode_blks, data)
    }

    constructor Init(d: Disk)
      ensures Valid()
    {
      fs := new Filesys.Init(d);
      data := map ino | ino_ok(ino) :: [];
    }

    constructor Recover(jrnl_: Jrnl)
      requires Filesys.Valid_basics(jrnl_)
      ensures fs.jrnl == jrnl_
    {
      fs := new Filesys.Recover(jrnl_);
    }

    // like fs.getInodeBlk but expressed at this abstraction level
    // trims the result if necessary to only include file data
    method getInodeBlock(txn: Txn, ino: Ino, i: Inode.Inode, off: uint64) returns (bs: Bytes)
      modifies {}
      requires Valid()
      requires txn.jrnl == fs.jrnl
      requires fs.is_inode(ino, i)
      requires off % 4096 == 0
      requires off as nat < |data[ino]|
      ensures fresh(bs)
      ensures off as nat + |bs.data| <= |data[ino]|
      ensures |bs.data| <= 4096
      ensures if |data[ino]| > off as nat + 4096 then
      (|bs.data| == 4096 && bs.data == data[ino][off as nat..off as nat + 4096])
      else bs.data == data[ino][off as nat..]
    {
      var blkoff: nat := off as nat / 4096;
      ghost var off': nat := blkoff * 4096;
      assert off' == off as nat;

      bs := fs.getInodeBlk(txn, ino, i, blkoff);
      assert Valid();

      ghost var blks := fs.inode_blks[ino].used_blocks();
      assert bs.data == blks[blkoff];
      fs.inode_blks[ino].used_blocks_valid();
      assert off' + 4096 <= |C.concat(blks)| &&
        bs.data == C.concat(blks)[off'..off'+4096] by {
        C.concat_homogeneous_one_list(blks, blkoff, 4096);
        reveal_inode_data();
      }

      if off + 4096 > i.sz {
        bs.Subslice(0, i.sz - off);
        ghost var bytes_read := (i.sz - off) as nat;
        C.double_subslice_auto(C.concat(blks));
        assert |bs.data| < 4096;
        assert off as nat + |bs.data| == |data[ino]|;
        reveal_inode_data();
        return;
      }

      assert bs.data == data[ino][off..off+4096] by {
        reveal_inode_data();
      }
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

      var blkoff: uint64 := off / 4096;
      var off' := blkoff * 4096;

      bs := getInodeBlock(txn, ino, i, off');

      if off % 4096 + len <= bs.Len() {
        // we finished the entire read
        bs.Subslice(off % 4096, off % 4096 + len);

        var _ := txn.Commit();
        if |data[ino]| > off' as nat + 4096 {
          C.double_subslice_auto(data[ino]);
        }
        return;
      }

      assert bs.data == data[ino][off'..off' + 4096];
      bs.Subslice(off % 4096, 4096);
      assert bs.data == data[ino][off..off' + 4096] by {
        C.double_subslice_auto(data[ino]);
      }
      var read_bytes: uint64 := bs.Len();

      var off'' := off' + 4096;
      var bs2 := getInodeBlock(txn, ino, i, off'');
      bs2.Subslice(0, len - read_bytes);
      ghost var bs2_upper_bound: nat := off'' as nat + (len - read_bytes) as nat;
      assert bs2.data == data[ino][off''..bs2_upper_bound] by {
        C.double_subslice_auto(data[ino]);
      }

      bs.AppendBytes(bs2);

      assert (off + len) as nat == bs2_upper_bound;
      calc {
        bs.data;
        data[ino][off..off''] + data[ino][off''..bs2_upper_bound];
        data[ino][off..off + len];
      }

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
      requires d.Valid()
      requires 0 < d.num_used
    {
      d.blks[d.num_used-1]
    }

    function set_last_block(d: InodeData, b: Block): InodeData
      requires d.Valid()
      requires 0 < d.num_used
    {
      var blks := d.blks;
      var off := d.num_used-1;
      d.(blks:=blks[off := b])
    }

    lemma get_set_last(d: InodeData, b: Block)
      requires d.Valid()
      requires 0 < d.num_used
      requires is_block(b)
      ensures get_last_block(set_last_block(d, b)) == b
    {}

    lemma inode_data_splice_last(d: InodeData, d': InodeData, bs: seq<byte>)
      requires 0 < d.num_used
      requires 0 < |bs|
      requires d.sz % 4096 + |bs| <= 4096
      requires d.Valid() && d'.Valid()
      requires (assert is_block(get_last_block(d));
                d' == set_last_block(d, C.splice(get_last_block(d), d.sz % 4096, bs)).(sz:=d.sz + |bs|))
      // don't see exactly why this would be true
      requires d'.num_used == d.num_used
      ensures inode_data(d') == inode_data(d) + bs
    {
      reveal_inode_data();
      ghost var blks := d.used_blocks();
      ghost var blks' := d'.used_blocks();
      assert is_block(C.last(blks));
      assert C.last(blks') == get_last_block(d');
      get_set_last(d, C.splice(get_last_block(d), d.sz % 4096, bs));
      assert C.last(blks') == C.splice(C.last(blks), d.sz % 4096, bs);

      C.concat_split_last(blks);
      d.used_blocks_valid();
      C.concat_homogeneous_len(blks, 4096);
      C.concat_split_last(blks');
      C.concat_homogeneous_len(C.without_last(blks'), 4096);
      calc {
        inode_data(d');
        (C.concat(C.without_last(blks')) + C.last(blks'))[..d'.sz];
        C.concat(C.without_last(blks')) + C.last(blks')[..d'.sz - (|blks'|-1) * 4096];
        C.concat(C.without_last(blks)) + C.last(blks')[..d'.sz - (|blks'|-1) * 4096];
      }
    }

    lemma inode_data_replace_last(d: InodeData, d': InodeData, bs: seq<byte>, new_bytes: nat)
      requires 0 < d.num_used
      requires d.sz % 4096 == 0 && |bs| == 4096
      requires d.Valid() && d'.Valid()
      requires (assert is_block(get_last_block(d));
                d' == set_last_block(d, bs).(sz:=d.sz - 4096 + new_bytes))
      requires d'.num_used == d.num_used
      ensures inode_data(d') == inode_data(d)[..d.sz - 4096] + bs[..new_bytes]
    {
      reveal_inode_data();
      ghost var blks := d.used_blocks();
      ghost var blks' := d'.used_blocks();
      C.concat_split_last(blks);
      d.used_blocks_valid();
      C.concat_homogeneous_len(blks, 4096);
      C.concat_split_last(blks');
      assert C.concat(C.without_last(blks)) == inode_data(d)[..d.sz - 4096];
    }

    method writeLastBlock(txn: Txn, ino: Ino, i: Inode.Inode, bs: Bytes) returns (i': Inode.Inode)
      modifies Repr()
      requires ValidIno(ino, i) ensures ValidIno(ino, i')
      requires txn.jrnl == fs.jrnl
      requires i.sz % 4096 == 0
      requires 4096 <= i.sz
      requires bs.Valid()
      requires 0 < bs.Len() <= 4096
      ensures (var d := old(data[ino]);
            data == old(data[ino:= d[..|d|-4096] + bs.data]))
    {
        var bn := i.blks[i.used_blocks-1];
        var blk := NewBytes(4096);
        blk.CopyTo(0, bs);
        fs.writeDataBlock(txn, bn, blk, ino, i.used_blocks-1);
        i' := i.(sz:=i.sz - 4096 + bs.Len());
        // this truncates the inode, which growInode grows for the sake of
        // preserving the complete inode invariant
        fs.writeInodeSz(txn, ino, i, i');

        ghost var ino_d := data[ino];
        ghost var stable_d := ino_d[..|ino_d|-4096];
        data := data[ino:= stable_d + bs.data];

        ghost var d' := fs.inode_blks[ino];
        assert inode_data(d') == stable_d + bs.data by {
          inode_data_replace_last(old(fs.inode_blks[ino]), fs.inode_blks[ino], blk.data, |bs.data|);
          assert blk.data[..|bs.data|] == bs.data;
        }
    }

    method growInodeAligned(txn: Txn, ino: Ino, i: Inode.Inode)
      returns (ok:bool, i': Inode.Inode, ghost b: Block)
      modifies Repr()
      requires ValidIno(ino, i) ensures ValidIno(ino, i')
      requires txn.jrnl == fs.jrnl
      requires i.sz % 4096 == 0
      requires i.sz as nat <= 13*4096
      ensures ok ==> is_block(b)
      ensures ok ==> data == old(data[ino:=data[ino] + b])
      ensures !ok ==> data == old(data)
    {
      ghost var d0 := fs.inode_blks[ino];
      if i.used_blocks < |i.blks| {
        i' := fs.useFreeBlock(txn, ino, i);
      } else {
        var bn;
        ok, i', bn := fs.appendToInode(txn, ino, i);
        if !ok {
          ok := false;
          return;
        }
      }
      ok := true;
      ghost var d' := fs.inode_blks[ino];
      b := C.last(d'.used_blocks());
      // this assertion should join the two branches above
      assert d'.used_blocks() == d0.used_blocks() + [b];

      data := data[ino := data[ino] + b];
      assert ValidIno(ino, i') by {
        C.concat_app1(d0.used_blocks(), b);
        inode_data_aligned(d0);
        inode_data_aligned(d');
        assert inode_data(d') == inode_data(d0) + b;
      }
    }

    method appendAligned(txn: Txn, ino: Ino, i: Inode.Inode, bs: Bytes) returns (ok:bool, i': Inode.Inode)
      modifies Repr()
      requires ValidIno(ino, i) ensures ValidIno(ino, i')
      requires txn.jrnl == fs.jrnl
      requires fs.is_inode(ino, i)
      requires i.sz % 4096 == 0
      requires bs.Valid()
      requires 0 < bs.Len() <= 4096
      requires i.sz as nat + |bs.data| <= 14*4096
      ensures ok ==> data == old(data[ino:=data[ino] + bs.data])
      ensures !ok ==> data == old(data)
    {
      // add some garbage data to the end of the inode
      ghost var b;
      ok, i', b := growInodeAligned(txn, ino, i);
      if !ok {
        return;
      }
      ok := true;

      label post_grow:
        // avoid unused label in Go
        //
        // see https://github.com/dafny-lang/dafny/issues/1093
      { break post_grow; }

      assert data[ino][..old(fs.inode_blks[ino].sz)] == old(data[ino]);

      i' := writeLastBlock(txn, ino, i', bs);
    }

    method appendAtEnd(txn: Txn, ino: Ino, i: Inode.Inode, bs: Bytes)
      returns (i': Inode.Inode, ghost written: nat, bs': Bytes)
      modifies Repr(), bs
      requires txn.jrnl == fs.jrnl
      requires ValidIno(ino, i) ensures ValidIno(ino, i')
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
      var blkoff: nat := i.used_blocks-1;
      var blk := fs.getInodeBlk(txn, ino, i, blkoff);
      assert |bs.data| <= |old(bs.data)|;
      assert |bs.data| <= remaining_space as nat;
      blk.CopyTo(i.sz % 4096, bs);
      var bn := i.blks[blkoff];
      fs.writeDataBlock(txn, bn, blk, ino, blkoff);

      i' := i.(sz := i.sz + bs.Len());
      assert i'.Valid();
      fs.writeInodeSz(txn, ino, i, i');

      data := data[ino := data[ino] + bs.data];
      assert ValidIno(ino, i') by {
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
      if i.sz + bs.Len() >= 14*4096 {
        ok := false;
        return;
      }
      if bs.Len() == 0 {
        ok := true;
        assert bs.data == [];
        assert data[ino] == data[ino] + bs.data;
        return;
      }

      fs.startInode(ino, i);

      ghost var written;
      var bs';
      i, written, bs' := appendAtEnd(txn, ino, i, bs);
      if bs'.Len() == 0 {
        ok := true;
        fs.finishInode(txn, ino, i);
        var _ := txn.Commit();
        assert old(bs.data[..written]) == old(bs.data);
        return;
      }
      assert i.sz % 4096 == 0;
      assert fs.is_cur_inode(ino, i);

      // we still need to write bs'
      assert data[ino] + bs'.data == old(data[ino] + bs.data);

      // TODO: this can abort after preparing the transaction; do we want to support that?
      ok, i := appendAligned(txn, ino, i, bs');
      if !ok {
        fs.finishInode(txn, ino, i);
        return;
      }
      fs.finishInode(txn, ino, i);
      var _ := txn.Commit();
    }
  }
}
