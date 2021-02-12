include "fs.dfy"
include "ind_block.dfy"

module IndFs
{
  import opened Machine
  import opened ByteSlice
  import opened FsKinds
  import opened JrnlTypes
  import opened JrnlSpec
  import opened Fs
  import opened Marshal
  import opened IndBlocks
  import C = Collections

  datatype preIdx = direct(k: nat) | indirect(k: nat, m: nat)
  {
    predicate Valid()
    {
      match this {
        case direct(k) => k < 10
        case indirect(k, m) => k < 5 && m < 512
      }
    }

    function flat(): nat
      requires Valid()
    {
      match this {
        case direct(k) => k
        case indirect(k, m) => 10 + k * 512 + m
      }
    }

    static function from_flat(n: nat): (i:Idx)
      requires n < 10 + 5*512
      ensures i.Valid()
    {
      if n < 10 then
        direct(n)
      else (
        var x := n-10;
        indirect(x/512, x % 512)
      )
    }

    lemma to_from_flat()
      requires Valid()
      ensures from_flat(this.flat()) == this
    {}

    static lemma from_to_flat(n: nat)
      requires n < 10 + 5*512
      ensures from_flat(n).flat() == n
    {}
  }

  type Idx = i:preIdx | i.Valid() witness direct(0)

  type Meta = s:seq<IndBlknos> | |s| == 5 witness C.repeat(indBlknos0, 5)
  const meta0: Meta := C.repeat(indBlknos0, 5)

  function meta_blknos(m: Meta): seq<Blkno>
  {
    C.concat(m)
  }

  datatype IndInodeData = IndInodeData(sz: nat, blks: seq<Block>)
  {
    static const zero: IndInodeData := IndInodeData(0, C.repeat(block0, 10 + 5*512))

    predicate Valid()
    {
      && sz <= Inode.MAX_SZ
      && |blks| == 10 + 5 * 512
    }

    static lemma zero_valid()
      ensures zero.Valid()
    {}
  }

  predicate indblknos_ok(bns: IndBlknos)
  {
    forall k | 0 <= k < 512 :: blkno_ok(bns[k])
  }

  predicate meta_ok?(meta: Meta)
  {
    forall k: nat | k < 5 :: indblknos_ok(meta[k])
  }

  class IndFilesys
  {
    ghost var ino_meta: map<Ino, Meta>
    ghost var ino_data: map<Ino, IndInodeData>
    const fs: Filesys

    function Repr(): set<object>
    {
      {this} + fs.Repr()
    }

    predicate ValidMeta()
      reads this
    {
      && ino_dom(ino_meta)
      && (forall ino | ino_ok(ino) :: meta_ok?(ino_meta[ino]))
    }

    predicate ValidData()
      reads this
    {
      && ino_dom(ino_data)
      && (forall ino | ino_ok(ino) :: ino_data[ino].Valid())
    }

    // this ensures inodes are separate from each other, but not that inode
    // metadata is separate from inode data
    predicate {:opaque} ValidOwnership()
      reads Repr()
      requires fs.Valid()
      requires ino_dom(ino_meta)
    {
      forall ino: Ino | ino_ok(ino) ::
        (forall bn | bn in meta_blknos(ino_meta[ino]) ::
        bn != 0 ==>
        && blkno_ok(bn)
        && fs.block_used[bn] == Some(ino))
    }

    // this is a strange definition for doubly-indirect blocks: we can't exactly
    // reach the metadata for the inode, only the first layer of metadata (after
    // that we have to resolve through the data_blocks, just like we currently
    // do to get from Meta to IndInodeData)
    static predicate meta_in_inode(d: InodeData, meta: Meta)
      requires d.Valid()
    {
      forall k | 0 <= k < 5 :: block_has_blknos(d.blks[10+k], meta[k])
    }

    static predicate ino_ind_match?(
      d: InodeData, meta: Meta, id: IndInodeData,
      // all data blocks for looking up data from meta block numbers
      data_block: map<Blkno, Block>)
      requires blkno_dom(data_block)
      requires meta_ok?(meta)
      requires id.Valid()
    {
      && d.Valid()
      && id.sz == d.sz
      && meta_in_inode(d, meta)
      && forall n | 0 <= n < 10 + 5*512 ::
      (match Idx.from_flat(n) {
        case direct(k) => d.blks[k] == id.blks[n]
        case indirect(k, m) =>
          zero_lookup(data_block, C.to_seq(meta[k])[m]) == id.blks[n]
      })
    }

    predicate {:opaque} Valid_ino_data()
      reads this.Repr()
      requires fs.Valid()
      requires ino_dom(ino_meta)
      requires ino_dom(ino_data)
      requires ValidMeta()
      requires ValidData()
    {
      forall ino | ino_ok(ino) ::
        ino_ind_match?(fs.inode_blks[ino], ino_meta[ino], ino_data[ino], fs.data_block)
    }

    predicate Valid()
      reads this.Repr()
    {
      && fs.Valid()
      && ValidMeta()
      && ValidData()
      && Valid_ino_data()
    }

    constructor(d: Disk)
      ensures Valid()
    {
      this.fs := new Filesys.Init(d);
      this.ino_meta := map ino: Ino | ino_ok(ino) :: meta0;
      this.ino_data := map ino: Ino | ino_ok(ino) :: IndInodeData.zero;
      new;
      IndInodeData.zero_valid();
      assert Valid_ino_data() by {
        assert meta_in_inode(InodeData.zero, meta0) by {
          zero_block_blknos();
        }
        assert ino_ind_match?(InodeData.zero, meta0, IndInodeData.zero,
          fs.data_block);
        reveal Valid_ino_data();
      }
    }
  }

}
