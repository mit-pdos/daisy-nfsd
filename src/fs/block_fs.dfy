include "indirect_fs.dfy"

module BlockFs
{
  import opened Machine
  import opened ByteSlice
  import opened FsKinds
  import opened JrnlTypes
  import opened JrnlSpec
  import opened IndirectPos
  import opened IndFs
  import Inode
  import opened MemInodes
  import C = Collections

  datatype preInodeData = InodeData(blks: seq<Block>)
  {
    static const preZero := InodeData(C.repeat(block0, config.total))
    static const zero: InodeData := preZero

    predicate Valid()
    {
      |blks| == config.total
    }
  }
  type InodeData = x:preInodeData | x.Valid() witness preInodeData.preZero

  function {:opaque} inode_blocks(ino: Ino, data: imap<Pos, Block>): InodeData
    requires data_dom(data)
  {
    var blks := seq(config.total,
      (n:nat) requires n < config.total => data[Pos.from_flat(ino, n as uint64)]);
    InodeData(blks)
  }

  predicate is_lba(i: uint64)
  {
    i as nat < config.total
  }

  function {:opaque} block_data(data: imap<Pos, Block>): (m:map<Ino, InodeData>)
    requires data_dom(data)
    ensures InodeFs.ino_dom(m)
  {
    map ino:Ino :: inode_blocks(ino, data)
  }

  // public
  method New(d: Disk) returns (fs: IndFilesys)
    ensures fs.ValidQ()
    ensures fresh(fs.Repr)
    ensures block_data(fs.data) == map ino: Ino {:trigger} :: InodeData.zero
    ensures fs.metadata == map ino: Ino {:trigger} :: Inode.Meta.zero
  {
    fs := new IndFilesys.Init(d);
    reveal inode_blocks();
    reveal block_data();
    assert forall ino: Ino :: inode_blocks(ino, fs.data) == InodeData.zero;
  }

  // public
  method Read(fs: IndFilesys, txn: Txn, ghost ino: Ino, i: MemInode, n: uint64)
    returns (bs: Bytes)
    requires fs.ValidIno(ino, i)
    requires fs.has_jrnl(txn)
    requires is_lba(n)
    ensures fresh(bs)
    ensures bs.data == block_data(fs.data)[ino].blks[n]
  {
    bs := fs.read(txn, Pos.from_flat(ino, n), i);
    reveal inode_blocks();
    reveal block_data();
  }

  lemma map_update_eq<K,V>(m1: map<K, V>, k0: K, v: V, m2: map<K, V>)
    requires forall k: K :: k in m1 <==> k in m2
    requires forall k: K | k in m1 && k != k0 :: m1[k] == m2[k]
    requires k0 in m2 && m2[k0] == v
    ensures m2 == m1[k0 := v]
  {}

  lemma block_data_update(data: imap<Pos, Block>, ino: Ino, n: uint64, blk: Block)
    requires is_lba(n)
    requires data_dom(data)
    ensures inode_blocks(ino, data[Pos.from_flat(ino, n) := blk]).blks ==
            inode_blocks(ino, data).blks[n := blk]
  {
    reveal inode_blocks();
    ghost var data' := data[Pos.from_flat(ino, n) := blk];
    ghost var n0 := n;
    ghost var d0 := inode_blocks(ino, data);
    ghost var d := inode_blocks(ino, data');
    forall n | is_lba(n)
      ensures d.blks[n] == d0.blks[n0 := blk][n]
    {
      Idx.from_flat_inj(n, n0);
      // if n == n0 {}
      // else {
      //   assert Idx.from_flat(n) != Idx.from_flat(n0) by {
      //     Idx.from_flat_inj(n, n0);
      //   }
      // }
    }
  }

  // an update to an ino0 Pos doesn't affect ino
  lemma block_data_update_other(data: imap<Pos, Block>, ino0: Ino, ino: Ino, n: uint64, blk: Block)
    requires is_lba(n)
    requires ino != ino0
    requires data_dom(data)
    ensures inode_blocks(ino, data[Pos.from_flat(ino0, n) := blk]) ==
            inode_blocks(ino, data)
  {
    reveal inode_blocks();
  }

  // public
  method block_write(fs: IndFilesys, txn: Txn, ghost ino: Ino, i: MemInode, n: uint64, blk: Bytes)
    returns (ok: bool)
    modifies fs.Repr, i.Repr
    requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i)
    requires fs.has_jrnl(txn)
    requires is_lba(n)
    requires is_block(blk.data)
    ensures fs.metadata == old(fs.metadata)
    ensures ok ==> block_data(fs.data) == old(
        var data := block_data(fs.data);
        var d0 := data[ino];
        data[ino := d0.(blks := d0.blks[n := blk.data])])
    ensures blk.data == old(blk.data)
    ensures !ok ==> block_data(fs.data) == old(block_data(fs.data))
  {
    ok := fs.write(txn, Pos.from_flat(ino, n), i, blk);
    if !ok {
      return;
    }

    assert blk.data == old(blk.data);
    reveal block_data();

    ghost var d0 := old(block_data(fs.data)[ino]);
    ghost var d := block_data(fs.data)[ino];
    assert d.blks == d0.blks[n := blk.data] by {
      block_data_update(old(fs.data), ino, n, blk.data);
    }

    ghost var ino0: Ino := ino;
    forall ino:Ino | ino != ino0
      ensures block_data(fs.data)[ino] == old(block_data(fs.data)[ino])
    {
      block_data_update_other(old(fs.data), ino0, ino, n, blk.data);
    }
  }

  lemma splice_repeat_one_more<T>(s: seq<T>, start: nat, count: nat, x: T)
    requires start + count < |s|
    ensures C.splice(s, start, C.repeat(x, count+1)) ==
            C.splice(s, start, C.repeat(x, count))[start + count := x]
  {}

  method block_zero_free(fs: IndFilesys, txn: Txn, ghost ino: Ino, i: MemInode,
    start: uint64, len: uint64)
    returns (done: bool)
    modifies fs.Repr, i.Repr
    requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i)
    requires fs.has_jrnl(txn)
    //requires start + len <= config.total
    requires start as nat + len as nat <= config.total
    ensures forall ino':Ino | ino != ino' :: block_data(fs.data)[ino'] == old(block_data(fs.data)[ino'])
    ensures forall off:uint64 | off < start ::
      block_data(fs.data)[ino].blks[off] ==
      old(block_data(fs.data)[ino].blks[off])
    ensures fs.metadata == old(fs.metadata)
  {
    done := fs.zeroFrom(txn, start, len, ino, i);
    reveal inode_blocks();
    reveal block_data();
  }

  method block_checkZero(fs: IndFilesys, txn: Txn, ghost ino: Ino, i: MemInode,
    off: uint64, len: uint64)
    returns (ok: bool)
    requires fs.has_jrnl(txn)
    requires fs.ValidIno(ino, i);
    requires off as nat + len as nat <= config.total
    ensures ok ==> forall off': uint64 | off <= off' < (off + len) ::
      block_data(fs.data)[ino].blks[off'] == block0
  {
    ok := fs.checkZero(txn, off, len, ino, i);
    reveal inode_blocks();
    reveal block_data();
  }
}
