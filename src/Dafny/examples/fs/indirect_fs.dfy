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

  datatype preMeta = Meta(s: seq<IndBlknos>)
  {
    static const preZero := Meta(C.repeat(IndBlknos.zero, 5))
    static const zero: Meta := preZero

    predicate Valid()
    {
      |s| == 5
    }

    static function blknos_to_seq(s: IndBlknos): seq<Blkno> { s.s }

    function blknos(): seq<Blkno>
    {
      C.concat(C.seq_fmap(blknos_to_seq, this.s))
    }

    predicate unique_at(i1: nat, j1: nat, i2: nat, j2: nat)
      requires Valid()
      requires i1 < 5 && i2 < 5 && j1 < 512 && j2 < 512
    {
      s[i1].s[j1] != 0 ==> i1 == i2 && j1 == j2
    }

    predicate unique()
      requires Valid()
    {
      forall i1, j1, i2, j2 | 0 <= i1 < 5 && 0 <= i2 < 5 && 0 <= j1 < 512 && 0 <= j2 < 512 ::
        s[i1].s[j1] == s[i2].s[j2] ==> unique_at(i1, j1, i2, j2)
    }

    lemma unique_elim(i1: nat, j1: nat, i2: nat, j2: nat)
      requires Valid() && unique()
      requires i1 < 5 && i2 < 5 && j1 < 512 && j2 < 512
      ensures s[i1].s[j1] == s[i2].s[j2] ==> s[i1].s[j1] != 0 ==> i1 == i2 && j1 == j2
    {
    }

    lemma unique_alt1()
      requires Valid()
      ensures unique() ==> Inode.blks_unique(blknos())
    {
      if !unique() { return; }
      var s' := C.seq_fmap(blknos_to_seq, this.s);
      C.concat_homogeneous_spec_alt(s', 512);
      forall i1, i2 | 0 <= i1 < 5*512 && 0 <= i2 < 5*512
        ensures C.concat(s')[i1] == C.concat(s')[i2] ==>
        i1 == i2 || C.concat(s')[i1] == 0
      {
        unique_elim(i1/512, i1%512, i2/512, i2%512);
      }
      reveal Inode.blks_unique();
      assert blknos() == C.concat(s');
    }

    lemma unique_alt2()
      requires Valid()
      ensures Inode.blks_unique(blknos()) ==> unique()
    {
      if !Inode.blks_unique(blknos()) { return; }
      var s' := C.seq_fmap(blknos_to_seq, this.s);
      C.concat_homogeneous_spec_alt(s', 512);
      C.concat_homogeneous_spec(s', 512);
      reveal Inode.blks_unique();
      forall i1, j1, i2, j2 | 0 <= i1 < 5 && 0 <= i2 < 5 && 0 <= j1 < 512 && 0 <= j2 < 512 &&
      s[i1].s[j1] == s[i2].s[j2]
      ensures unique_at(i1, j1, i2, j2)
      {
        var k1 := i1*512 + j1;
        var k2 := i2*512 + j2;
        assert s[i1].s[j1] == C.concat(s')[k1];
        assert s[i2].s[j2] == C.concat(s')[k2];
        assert k1 == k2 || C.concat(s')[k1] == 0;
      }
    }

    lemma unique_alt()
      requires Valid()
      ensures unique() <==> Inode.blks_unique(blknos())
    {
      unique_alt1();
      unique_alt2();
    }
  }
  type Meta = s:preMeta | s.Valid() witness preMeta.preZero

  datatype IndInodeData = IndInodeData(sz: nat, blks: seq<Block>)
  {
    static const zero: IndInodeData := IndInodeData(0, C.repeat(block0, 10 + 5*512))
    static lemma zero_valid()
      ensures zero.Valid()
    {}

    predicate Valid()
    {
      && sz <= Inode.MAX_SZ
      && |blks| == 10 + 5 * 512
    }

  }

  predicate indblknos_ok(bns: IndBlknos)
  {
    forall k | 0 <= k < 512 :: blkno_ok(bns.s[k])
  }

  predicate meta_ok?(meta: Meta)
  {
    assert meta.Valid();
    forall k: nat | k < 5 :: indblknos_ok(meta.s[k])
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
        (forall bn | bn in ino_meta[ino].blknos() ::
        bn != 0 ==>
        && blkno_ok(bn)
        && fs.block_used[bn] == Some(ino))
    }

    static predicate blks_disjoint(blks1: seq<uint64>, blks2: seq<uint64>)
    {
      forall bn1, bn2 | bn1 in blks1 && bn2 in blks2 :: bn1 == bn2 ==> bn1 == 0
    }

    // TODO: also need uniqueness of metadata (maybe would be better to assign
    // every block a more precise role in fs.dfy itself, like Free | Data(ino) |
    // Metadata(ino, level); then this part would be unnecessary)
    predicate {:opaque} meta_disjoint_from_data()
      reads Repr()
      requires fs.Valid()
      requires ino_dom(ino_meta)
    {
      forall ino: Ino | ino_ok(ino) ::
        blks_disjoint(ino_meta[ino].blknos(), fs.inodes[ino].blks)
    }

    predicate {:opaque} meta_unique()
      reads this
      requires ino_dom(ino_meta)
    {
      forall ino: Ino | ino_ok(ino) :: ino_meta[ino].unique()
    }

    predicate Valid_meta_separation()
      reads Repr()
      requires fs.Valid()
      requires ino_dom(ino_meta)
    {
      && meta_disjoint_from_data()
      && meta_unique()
    }

    // this is a strange definition for doubly-indirect blocks: we can't exactly
    // reach the metadata for the inode, only the first layer of metadata (after
    // that we have to resolve through the data_blocks, just like we currently
    // do to get from Meta to IndInodeData)
    static predicate meta_in_inode(d: InodeData, meta: Meta)
      requires d.Valid()
    {
      assert meta.Valid();
      forall k | 0 <= k < 5 :: block_has_blknos(d.blks[10+k], meta.s[k])
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
          zero_lookup(data_block, meta.s[k].s[m]) == id.blks[n]
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
      && ValidOwnership()
      && Valid_meta_separation()
    }

    constructor(d: Disk)
      ensures Valid()
    {
      this.fs := new Filesys.Init(d);
      this.ino_meta := map ino: Ino | ino_ok(ino) :: Meta.zero;
      this.ino_data := map ino: Ino | ino_ok(ino) :: IndInodeData.zero;
      new;
      IndInodeData.zero_valid();
      assert Valid_ino_data() by {
        assert meta_in_inode(InodeData.zero, Meta.zero) by {
          zero_block_blknos();
        }
        assert ino_ind_match?(InodeData.zero, Meta.zero, IndInodeData.zero,
          fs.data_block);
        reveal Valid_ino_data();
      }
      forall ino: Ino | ino_ok(ino)
        ensures ino_meta[ino].blknos() == C.repeat(0 as Blkno, 5*512)
      {
        C.concat_repeat(0 as Blkno, 512, 5);
        C.repeat_seq_fmap_auto<IndBlknos, seq<Blkno>>();
        assert Meta.zero.blknos() == C.repeat(0 as Blkno, 5*512);
      }
      assert ValidOwnership() by {
        reveal ValidOwnership();
      }
      assert Valid_meta_separation() by {
        reveal meta_disjoint_from_data();
        reveal meta_unique();
      }
    }
  }

}
