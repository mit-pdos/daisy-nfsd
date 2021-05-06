include "../jrnl/jrnl.s.dfy"
include "../nonlin/roundup.dfy"
include "../machine/int_encoding.s.dfy"
include "../machine/bytes.s.dfy"
include "../util/marshal.i.dfy"

module FsKinds {
  import Arith
  import opened Machine
  import opened JrnlTypes
  import opened JrnlSpec
  import opened Kinds
  import opened KindsFacts
  import opened ByteSlice
  import IntEncoding
  import Round
  import Marshal

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

    // NOTE(tej): hack because otherwise non-linear arithmetic in
    // disk_size confuses Dafny and it doesn't know the sum is still a nat
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
    static const block_addr: uint64 := 513
    const data_bitmap_start: nat := 513 + 1 + inode_blocks
    const data_start: nat := data_bitmap_start + data_bitmaps

    const disk_size: nat := add_nats(data_start, num_data_blocks)
  }

  // we initialize the superblock this way to get named arguments
  const super := Super.zero.(inode_blocks:=30, data_bitmaps:=20)
  lemma super_valid()
    ensures super.Valid()
  {}
  lemma super_size()
    ensures super.num_inodes == 960;
    ensures super.num_data_blocks
        * 4096 / (1000*1000) == 2684 /* MB */
  {}

  // we need these to be a real constants because accessing any const in super
  // computes a big int every time it's referenced, which shows up in the CPU
  // profile...
  const super_num_data_blocks: uint64 := 20*(4096*8)
  const super_data_bitmap_start: uint64 := 513 + 1 + 30;
  const super_data_start: uint64 := 513 + 1 + 30 + 20;
  lemma super_consts_ok()
    ensures super_num_data_blocks as nat == super.num_data_blocks
    ensures super_data_bitmap_start as nat == super.data_bitmap_start
    ensures super_data_start as nat == super.data_start
  {}


  datatype SuperBlock = SuperBlock(info: Super, actual_blocks: uint64)
  {
    // a random number
    static const magic: uint64 := 0x5211cc92a57dd76b;

    predicate Valid()
    {
      info.Valid()
    }

    function enc(): seq<byte>
      requires Valid()
    {
      IntEncoding.le_enc64(magic) +
        IntEncoding.le_enc64(info.inode_blocks as uint64) +
        IntEncoding.le_enc64(info.data_bitmaps as uint64) +
        IntEncoding.le_enc64(actual_blocks) +
        C.repeat(0 as byte, 4096-(8*4))
    }

    method encode() returns (b: Bytes)
      requires Valid()
      ensures is_block(b.data)
      ensures b.data == enc()
    {
      b := NewBytes(4096);
      IntEncoding.UInt64Put(magic, 0, b);
      IntEncoding.UInt64Put(info.inode_blocks as uint64, 8, b);
      IntEncoding.UInt64Put(info.data_bitmaps as uint64, 16, b);
      IntEncoding.UInt64Put(actual_blocks as uint64, 24, b);
    }

    static method decode(b: Bytes, ghost sb0: SuperBlock) returns (sb: SuperBlock)
      requires sb0.Valid()
      requires b.data == sb0.enc()
      ensures sb == sb0
      // check at runtime super info has not changed
      ensures sb.info == super
    {
      var m := Marshal.UInt64Decode(b, 0, magic);
      if m != magic {
        assert false;
        if m == 0 {
          expect false, "magic is 0, file system seems to not be initialized";
        }
        expect false, "magic is incorrect, not a dafny-nfsd file system";
      }
      var inode_blocks := Marshal.UInt64Decode(b, 8, sb0.info.inode_blocks as uint64);
      expect inode_blocks == super.inode_blocks as uint64, "number of inode blocks has changed";
      var data_bitmaps := Marshal.UInt64Decode(b, 16, sb0.info.data_bitmaps as uint64);
      expect data_bitmaps as nat == super.data_bitmaps, "number of data bitmaps has changed";
      var actual_blocks := Marshal.UInt64Decode(b, 24, sb0.actual_blocks);
      return SuperBlock(Super(inode_blocks as nat, data_bitmaps as nat), actual_blocks);
    }
  }

  function zero_inode_witness(): (x:uint64)
    ensures ino_ok(x)
  {
    reveal ino_ok();
    0 as uint64
  }

  type Ino = ino:uint64 | ino_ok(ino) ghost witness zero_inode_witness()

  predicate blkno_ok(blkno: Blkno) { blkno as nat < super.num_data_blocks }
  predicate {:opaque} ino_ok(ino: uint64) { ino as nat < super.num_inodes }

  const SuperBlkAddr: Addr := Addr(Super.block_addr, 0);

  function method InodeBlk(ino: Ino): (bn':Blkno)
    ensures InodeBlk?(bn')
  {
    reveal ino_ok();
    513 + 1 + ino / 32
  }

  predicate InodeBlk?(bn: Blkno)
  {
    513 + 1 <= bn as nat < 513 + 1 + super.inode_blocks
  }

  lemma InodeBlk?_correct(bn: Blkno)
    ensures InodeBlk?(bn) <==> exists ino':Ino :: InodeBlk(ino') == bn
  {
    if InodeBlk?(bn) {
      var ino: Ino := (bn - 513 - 1) * 32;
      assert InodeBlk(ino) == bn;
    }
  }

  function method DataAllocBlk(bn: Blkno): (bn':Blkno)
    ensures blkno_ok(bn) ==> DataAllocBlk?(bn')
  {
    var bn' := super_data_bitmap_start + bn / (4096*8);
    if bn < super_num_data_blocks then (
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
      var bn' := (bn - (513 + 1 + super.inode_blocks) as uint64) * (4096*8);
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
    Addr(super_data_start+bn, 0)
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
      :: (if blkno == Super.block_addr
          then KindBlock
        else if InodeBlk?(blkno)
          then KindInode
        else if DataAllocBlk?(blkno)
          then KindBit
        else (assert DataBlk?(blkno); KindBlock)
      ) as Kind

  lemma fs_kinds_valid()
    ensures kindsValid(fs_kinds)
  {}

  lemma super_block_inbounds(jrnl: Jrnl)
    requires jrnl.Valid()
    requires jrnl.kinds == fs_kinds
    ensures SuperBlkAddr in jrnl.data && jrnl.size(SuperBlkAddr) == 4096*8
  {
    assert kindSize(KindBlock) == 4096*8;
    jrnl.in_domain(SuperBlkAddr);
    jrnl.has_size(SuperBlkAddr);
  }

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
