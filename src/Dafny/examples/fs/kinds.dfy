include "../../jrnl/jrnl.s.dfy"

module FsKinds {
  import Arith
  import opened Machine
  import opened JrnlSpec
  import opened Kinds

  type Ino = uint64

  const NumInodeBlocks: nat := 10
  const NumDataBitmapBlocks: nat := 1

  predicate blkno_ok(blkno: Blkno) { blkno as nat < NumDataBitmapBlocks * 4096*8 }
  predicate ino_ok(ino: Blkno) { ino as nat < 32*NumInodeBlocks }

  // disk layout, in blocks:
  //
  // 513 for the jrnl
  // NumInodeBlocks (each with 32 inodes)
  // NumDataBitmapBlocks
  // 4096*8 data blocks
  const DataBlockStart: uint64 := 513 +
    NumInodeBlocks as uint64
    + NumDataBitmapBlocks as uint64
  const NumBlocks: nat := DataBlockStart as nat +
    NumDataBitmapBlocks*4096*8
    // if you want to make a disk for the fs 40,000 blocks is a usable number
  lemma NumBlocks_upper_bound()
    ensures NumBlocks < 40_000
  {}

  function method InodeBlk(ino: Ino): Blkno
  {
    513 + ino / 32
  }

  function method InodeBlk?(bn: Blkno): bool
  {
    513 <= bn as nat < 513 + NumInodeBlocks
  }

  const DataAllocBlk: Blkno := 513 + NumInodeBlocks as uint64

  function method InodeAddr(ino: Ino): (a:Addr)
    requires ino_ok(ino)
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
  function method DataBitAddr(bn: uint64): Addr
    requires blkno_ok(bn)
  {
    Addr(DataAllocBlk, bn)
  }
  function method DataBlk(bn: uint64): (a:Addr)
    requires blkno_ok(bn)
    ensures a in addrsForKinds(fs_kinds)
  {
    assert fs_kinds[DataBlockStart+bn] == KindBlock;
    assert kindSize(KindBlock) == 4096*8;
    Arith.zero_mod(4096*8);
    reveal_addrsForKinds();
    Addr(DataBlockStart+bn, 0)
  }

  lemma InodeAddr_disjoint(ino: Ino)
    requires ino_ok(ino)
    ensures forall bn': Blkno | blkno_ok(bn') :: InodeAddr(ino) != DataBitAddr(bn')
    ensures forall bn': Blkno | blkno_ok(bn') :: InodeAddr(ino) != DataBlk(bn')
  {}

  lemma DataBitAddr_disjoint(bn: Blkno)
    requires blkno_ok(bn)
    ensures forall ino': Ino | ino_ok(ino') :: DataBitAddr(bn) != InodeAddr(ino')
    ensures forall bn': Blkno | blkno_ok(bn') :: DataBitAddr(bn) != DataBlk(bn')
  {}

  lemma DataBlk_disjoint(bn: Blkno)
    requires blkno_ok(bn)
    ensures forall ino': Ino | ino_ok(ino') :: DataBlk(bn) != InodeAddr(ino')
    ensures forall bn': Ino | blkno_ok(bn') :: DataBlk(bn) != DataBitAddr(bn')
  {}

  const fs_kinds: map<Blkno, Kind> :=
    // NOTE(tej): trigger annotation suppresses warning (there's nothing to
    // trigger on here, but also nothing is necessary)
    map blkno: Blkno |
      513 <= blkno as nat < NumBlocks
      :: (if InodeBlk?(blkno)
      then KindInode
      else if blkno == DataAllocBlk
        then KindBit
        else KindBlock) as Kind

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
    requires ino_ok(ino)
    ensures InodeAddr(ino) in jrnl.data && jrnl.size(InodeAddr(ino)) == 8*128
  {
    kind_inode_size();
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
  }

}
