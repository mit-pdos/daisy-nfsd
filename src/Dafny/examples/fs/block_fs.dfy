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

  function inode_data(ino: Ino, data: imap<Pos, Block>): InodeData
    requires ino_ok(ino)
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

  function block_data(data: imap<Pos, Block>): map<Ino, InodeData>
    requires data_dom(data)
  {
    map ino:Ino | ino_ok(ino) :: inode_data(ino, data)
  }

  method New(d: Disk) returns (fs: IndFilesys)
    ensures fs.ValidQ()
    ensures block_data(fs.data) == map ino: Ino | ino_ok(ino) :: InodeData.zero
  {
    fs := new IndFilesys(d);
    assert forall ino: Ino | ino_ok(ino) :: inode_data(ino, fs.data) == InodeData.zero;
  }

  // public
  method Read(fs: IndFilesys, txn: Txn, ino: Ino, n: nat)
    returns (bs: Bytes)
    modifies fs.fs
    requires fs.ValidQ() ensures fs.ValidQ()
    requires fs.has_jrnl(txn)
    requires ino_ok(ino)
    requires is_lba(n)
    ensures bs.data == block_data(fs.data)[ino].blks[n]
    // this should be unnecessary due to the precise modifies clause
    // ensures fs.state_unchanged()
  {
    var i := fs.startInode(txn, ino);
    bs := fs.read(txn, Pos.from_flat(ino, n), i);
    fs.finishInodeReadonly(ino, i);
  }

  lemma map_update_eq<K,V>(m1: map<K, V>, k0: K, v: V, m2: map<K, V>)
    requires forall k: K :: k in m1 <==> k in m2
    requires forall k: K | k in m1 && k != k0 :: m1[k] == m2[k]
    requires k0 in m2 && m2[k0] == v
    ensures m2 == m1[k0 := v]
  {}

  lemma block_data_update(data: imap<Pos, Block>, ino: Ino, n: nat, blk: Block)
    requires ino_ok(ino)
    requires is_lba(n)
    requires data_dom(data)
    ensures inode_data(ino, data[Pos.from_flat(ino, n) := blk]).blks ==
            inode_data(ino, data).blks[n := blk]
  {
    ghost var data' := data[Pos.from_flat(ino, n) := blk];
    ghost var n0 := n;
    ghost var d0 := inode_data(ino, data);
    ghost var d := inode_data(ino, data');
    forall n | is_lba(n)
      ensures d.blks[n] == d0.blks[n0 := blk][n]
    {
      if n == n0 {}
      else {
        assert Idx.from_flat(n) != Idx.from_flat(n0) by {
          Idx.from_flat_inj(n, n0);
        }
      }
    }
  }

  // an update to an ino0 Pos doesn't affect ino
  lemma block_data_update_other(data: imap<Pos, Block>, ino0: Ino, ino: Ino, n: nat, blk: Block)
    requires ino_ok(ino0) && ino_ok(ino) && ino0 != ino
    requires is_lba(n)
    requires data_dom(data)
    ensures inode_data(ino, data[Pos.from_flat(ino0, n) := blk]) ==
            inode_data(ino, data)
  {}

  // public
  method Write(fs: IndFilesys, txn: Txn, ino: Ino, i: Inode.Inode, n: nat, blk: Bytes)
    returns (ok: bool, i': Inode.Inode)
    modifies fs.Repr()
    requires fs.ValidIno(ino, i) ensures fs.ValidIno(ino, i')
    requires fs.has_jrnl(txn)
    requires is_lba(n)
    requires is_block(blk.data)
    ensures fs.metadata == old(fs.metadata)
    ensures ok ==> block_data(fs.data) == (
        var data := old(block_data(fs.data));
        var d0 := data[ino];
        data[ino := d0.(blks := d0.blks[n := blk.data])])
    ensures !ok ==> block_data(fs.data) == old(block_data(fs.data))
  {
    ok, i' := fs.write(txn, Pos.from_flat(ino, n), i, blk);
    if !ok {
      return;
    }

    assert blk.data == old(blk.data);

    ghost var d0 := old(block_data(fs.data)[ino]);
    ghost var d := block_data(fs.data)[ino];
    assert d.blks == d0.blks[n := blk.data] by {
      block_data_update(old(fs.data), ino, n, blk.data);
    }

    ghost var ino0 := ino;
    forall ino:Ino | ino_ok(ino) && ino != ino0
      ensures block_data(fs.data)[ino] == old(block_data(fs.data)[ino])
    {
      block_data_update_other(old(fs.data), ino0, ino, n, blk.data);
    }
  }
}
