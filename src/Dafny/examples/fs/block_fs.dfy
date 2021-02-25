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
      (n:nat) requires n < config.total => data[Pos.from_flat(ino, n)]);
    InodeData(blks)
  }

  predicate is_lba(i: int)
  {
    0 <= i < config.total
  }

  function {:opaque} block_data(data: imap<Pos, Block>): (m:map<Ino, InodeData>)
    requires data_dom(data)
    ensures Fs.ino_dom(m)
  {
    map ino:Ino :: inode_blocks(ino, data)
  }

  // public
  method New<InodeAllocState(!new)>(d: Disk) returns (fs: IndFilesys<InodeAllocState>)
    ensures fs.ValidQ()
    ensures fresh(fs.Repr)
    ensures block_data(fs.data) == map ino: Ino {:trigger} :: InodeData.zero
    ensures fs.metadata == map ino: Ino {:trigger} :: Inode.Meta(0, Inode.InvalidType)
    ensures fs.inode_owner() == map ino: Ino {:trigger} :: Fs.None
  {
    fs := new IndFilesys.Init(d);
    reveal inode_blocks();
    reveal block_data();
    assert forall ino: Ino :: inode_blocks(ino, fs.data) == InodeData.zero;
  }

  // public
  method Read<InodeAllocState(!new)>(fs: IndFilesys<InodeAllocState>, txn: Txn, ino: Ino, i: Inode.Inode, n: nat)
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

  lemma block_data_update(data: imap<Pos, Block>, ino: Ino, n: nat, blk: Block)
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
  lemma block_data_update_other(data: imap<Pos, Block>, ino0: Ino, ino: Ino, n: nat, blk: Block)
    requires is_lba(n)
    requires ino != ino0
    requires data_dom(data)
    ensures inode_blocks(ino, data[Pos.from_flat(ino0, n) := blk]) ==
            inode_blocks(ino, data)
  {
    reveal inode_blocks();
  }

  // workaround for https://github.com/dafny-lang/dafny/issues/1130
  class WriteHelper<T(!new)>
  {
  const fs: IndFilesys<T>
  constructor(fs: IndFilesys<T>)
    ensures this.fs == fs
  {
    this.fs := fs;
  }

  // public
  method Do(txn: Txn, ino: Ino, i: Inode.Inode, n: nat, blk: Bytes)
    returns (ok: bool, i': Inode.Inode)
    modifies fs.Repr
    requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i')
    requires fs.has_jrnl(txn)
    requires is_lba(n)
    requires is_block(blk.data)
    ensures fs.metadata == old(fs.metadata)
    ensures fs.inode_owner() == old(fs.inode_owner())
    ensures ok ==> block_data(fs.data) == old(
        var data := block_data(fs.data);
        var d0 := data[ino];
        data[ino := d0.(blks := d0.blks[n := blk.data])])
    ensures blk.data == old(blk.data)
    ensures !ok ==> block_data(fs.data) == old(block_data(fs.data))
  {
    ok, i' := fs.write(txn, Pos.from_flat(ino, n), i, blk);
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
  }
}
