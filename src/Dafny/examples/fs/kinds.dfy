include "../../jrnl/jrnl.s.dfy"
include "../../nonlin/roundup.dfy"

module FsKinds {
  import Arith
  import opened Machine
  import opened JrnlTypes
  import opened JrnlSpec
  import opened Kinds
  import Round

  datatype Super = Super(inode_blocks: nat, data_bitmaps: nat)
  {
    const num_inodes: nat := 32 * inode_blocks
    const num_data_blocks: nat := data_bitmaps * (4096*8)

    static const zero := Super(0, 0)

    predicate Valid()
    {
      && 0 < inode_blocks
      && 0 < data_bitmaps
      && disk_size < U64.MAX
    }

    // NOTE(tej): hack because otherwise non-linear arithmetic in num_data_blocks confuses Dafny and it doesn't know the sum is still a nat
    static function method add_nats(n1: nat, n2: nat): nat
    {
      n1 + n2
    }

    // prior to data, disk layout is:
    //
    // 513 blocks reserved for the journal
    // inode_blocks hold the inodes
    // data_bitmaps are allocators for the data blocks
    // inode_bitmaps are allocators for inodes
    //
    // these are followed by num_data_blocks data blocks
    const data_bitmap_start: nat := 513 + inode_blocks
    const data_start: nat := data_bitmap_start + data_bitmaps

    const disk_size: nat := add_nats(data_start, num_data_blocks)
  }

  // we initialize the superblock this way to get named arguments
  const super := Super.zero.(inode_blocks:=10, data_bitmaps:=6)
  lemma super_valid()
    ensures super.Valid()
  {}

  type Ino = ino:uint64 | ino_ok(ino)

  predicate blkno_ok(blkno: Blkno) { blkno as nat < super.num_data_blocks }
  predicate ino_ok(ino: uint64) { ino as nat < super.num_inodes }

  // if you want to make a disk for the fs this is a usable number
  lemma NumBlocks_upper_bound()
    ensures super.disk_size < 200_000
  {}

  function method InodeBlk(ino: Ino): (bn':Blkno)
    ensures InodeBlk?(bn')
  {
    513 + ino / 32
  }

  predicate InodeBlk?(bn: Blkno)
  {
    513 <= bn as nat < 513 + super.inode_blocks
  }

  lemma InodeBlk?_correct(bn: Blkno)
    ensures InodeBlk?(bn) <==> exists ino':Ino :: InodeBlk(ino') == bn
  {
    if InodeBlk?(bn) {
      var ino: Ino := (bn - 513) * 32;
      assert InodeBlk(ino) == bn;
    }
  }

  function method DataAllocBlk(bn: Blkno): (bn':Blkno)
    ensures blkno_ok(bn) ==> DataAllocBlk?(bn')
  {
    var bn' := super.data_bitmap_start as uint64 + bn / (4096*8);
    if bn as nat < super.data_bitmaps*(4096*8) then (
      Arith.div_incr(bn as nat, super.data_bitmaps, 4096*8);
      bn'
    ) else bn'
  }

  predicate DataAllocBlk?(bn: Blkno)
  {
    var start := super.data_bitmap_start;
    start <= bn as nat < start + super.data_bitmaps
  }

  lemma DataAllocBlk?_correct(bn: Blkno)
    ensures DataAllocBlk?(bn) <==> exists bn' :: blkno_ok(bn') && DataAllocBlk(bn') == bn
  {
    if DataAllocBlk?(bn) {
      var bn' := (bn - (513 + super.inode_blocks) as uint64) * (4096*8);
      assert blkno_ok(bn');
      assert DataAllocBlk(bn') == bn;
    }
  }

  function method {:opaque} InodeAddr(ino: Ino): (a:Addr)
    ensures a in addrsForKinds(fs_kinds)
  {
    kind_inode_size();
    var ino_blk := InodeBlk(ino);
    var ino_off := ino % 32;
    assert fs_kinds[ino_blk] == KindInode;
    Arith.mul_assoc(ino_off as nat, 128, 8);
    Arith.mul_r_strictly_incr(ino as nat, 128*8, 32);
    assert ino_off*128*8 < 4096*8;
    Arith.mul_mod(ino as nat, 128*8);
    assert kindSize(KindInode) == 128*8;
    reveal_addrsForKinds();
    Addr(ino_blk, ino_off*128*8)
  }
  function method DataBitAddr(bn: Blkno): Addr
    requires blkno_ok(bn)
  {
    Addr(DataAllocBlk(bn), bn % (4096*8))
  }
  function method {:opaque} DataBlk(bn: Blkno): (a:Addr)
    requires blkno_ok(bn)
    ensures a in addrsForKinds(fs_kinds)
  {
    assert fs_kinds[super.data_start as uint64+bn] == KindBlock;
    assert kindSize(KindBlock) == 4096*8;
    Arith.zero_mod(4096*8);
    reveal_addrsForKinds();
    Addr(super.data_start as uint64+bn, 0)
  }
  predicate DataBlk?(bn: uint64)
  {
    super.data_start <= bn as nat
  }

  lemma InodeAddr_inj()
    ensures forall ino: Ino, ino': Ino ::
    InodeAddr(ino) == InodeAddr(ino') ==> ino == ino'
  {
    reveal_InodeAddr();
  }

  lemma InodeAddr_disjoint(ino: Ino)
    ensures forall bn': Blkno | blkno_ok(bn') :: InodeAddr(ino) != DataBitAddr(bn')
    ensures forall bn': Blkno | blkno_ok(bn') :: InodeAddr(ino) != DataBlk(bn')
  {
    reveal_DataBlk();
    reveal_InodeAddr();
    forall bn': Blkno | blkno_ok(bn')
      ensures InodeAddr(ino) != DataBitAddr(bn')
    {
      assert InodeBlk?(InodeAddr(ino).blkno);
      assert DataAllocBlk?(DataBitAddr(bn').blkno);
    }
  }

  lemma DataBitAddr_disjoint(bn: Blkno)
    requires blkno_ok(bn)
    ensures forall ino': Ino :: DataBitAddr(bn) != InodeAddr(ino')
    ensures forall bn': Blkno | blkno_ok(bn') :: DataBitAddr(bn) != DataBlk(bn')
  {
    reveal_DataBlk();
    reveal_InodeAddr();
  }

  lemma DataBlk_disjoint(bn: Blkno)
    requires blkno_ok(bn)
    ensures forall ino': Ino :: DataBlk(bn) != InodeAddr(ino')
    ensures forall bn': Blkno | blkno_ok(bn') :: DataBlk(bn) != DataBitAddr(bn')
  {
    reveal_DataBlk();
    reveal_InodeAddr();
  }

  ghost const fs_kinds: map<Blkno, Kind> :=
    map blkno: Blkno |
      513 <= blkno as nat < super.disk_size
      :: (if InodeBlk?(blkno)
          then KindInode
        else if DataAllocBlk?(blkno)
          then KindBit
        else (assert DataBlk?(blkno); KindBlock)
      ) as Kind

  lemma fs_kinds_valid()
    ensures kindsValid(fs_kinds)
  {}

  lemma blkno_bit_inbounds(jrnl: Jrnl)
    requires jrnl.Valid()
    requires jrnl.kinds == fs_kinds
    ensures forall bn :: blkno_ok(bn) ==> DataBitAddr(bn) in jrnl.data && jrnl.size(DataBitAddr(bn)) == 1
  {
    forall bn | blkno_ok(bn)
      ensures DataBitAddr(bn) in jrnl.data
    {
      ghost var addr := DataBitAddr(bn);
      jrnl.in_domain(addr);
      jrnl.has_size(addr);
    }
  }

  lemma inode_inbounds(jrnl: Jrnl, ino: Ino)
    requires jrnl.Valid()
    requires jrnl.kinds == fs_kinds
    ensures InodeAddr(ino) in jrnl.data && jrnl.size(InodeAddr(ino)) == 8*128
  {
    kind_inode_size();
    reveal_InodeAddr();
    ghost var addr := InodeAddr(ino);
    jrnl.in_domain(addr);
    jrnl.has_size(addr);
  }

  lemma datablk_inbounds(jrnl: Jrnl, bn: Blkno)
    requires jrnl.Valid()
    requires jrnl.kinds == fs_kinds
    requires blkno_ok(bn)
    ensures DataBlk(bn) in jrnl.data && jrnl.size(DataBlk(bn)) == 8*4096
  {
    ghost var addr := DataBlk(bn);
    reveal_addrsForKinds();
    jrnl.in_domain(addr);
    jrnl.has_size(addr);
    reveal_DataBlk();
  }

}
