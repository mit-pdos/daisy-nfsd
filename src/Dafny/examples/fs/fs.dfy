include "../../util/marshal.i.dfy"
include "../../jrnl/jrnl.s.dfy"
include "inode.dfy"

module Fs {
  import Inode
  import C = Collections
  import Arith
  import Round
  import opened Machine
  import opened ByteSlice
  import opened JrnlSpec
  import opened Kinds
  import opened Marshal

  type Ino = uint64

  predicate blkno_ok(blkno: Blkno) { blkno < 4096*8 }
  predicate ino_ok(ino: Blkno) { ino < 32 }

  // disk layout, in blocks:
  //
  // 513 for the jrnl
  // 1 inode block (32 inodes)
  // 1 bitmap block
  // 4096*8 data blocks
  const NumBlocks: nat := 513 + 1 + 1 + 4096*8
    // if you want to make a disk for the fs 40,000 blocks is a usable number
  lemma NumBlocks_upper_bound()
    ensures NumBlocks < 40_000
  {}

  const InodeBlk: Blkno := 513
  const DataAllocBlk: Blkno := 514

  function method InodeAddr(ino: Ino): (a:Addr)
    requires ino_ok(ino)
    ensures a in addrsForKinds(fs_kinds)
  {
    kind_inode_size();
    assert fs_kinds[InodeBlk] == KindInode;
    Arith.mul_assoc(ino as nat, 128, 8);
    Arith.mul_r_strictly_incr(ino as nat, 128*8, 32);
    assert ino*128*8 < 4096*8;
    Arith.mul_mod(ino as nat, 128*8);
    assert kindSize(KindInode) == 128*8;
    Addr(InodeBlk, ino*128*8)
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
    assert fs_kinds[513+2+bn] == KindBlock;
    assert kindSize(KindBlock) == 4096*8;
    Arith.zero_mod(4096*8);
    Addr(513+2+bn, 0)
  }

  const fs_kinds: map<Blkno, Kind> :=
    // NOTE(tej): trigger annotation suppresses warning (there's nothing to
    // trigger on here, but also nothing is necessary)
    map blkno: Blkno {:trigger} |
      513 <= blkno as nat < NumBlocks
      :: (if blkno == InodeBlk
      then KindInode
      else if blkno == DataAllocBlk
        then KindBit
        else KindBlock) as Kind

  lemma fs_kinds_valid()
    ensures kindsValid(fs_kinds)
  {}

  datatype Option<T> = Some(x:T) | None

  class Filesys
  {

    // spec state
    ghost var data: map<Ino, seq<byte>>;

    // intermediate abstractions

    // slightly more physical representation of an inode as a sequence of data
    // blocks (without size, that's in this.inodes)
    ghost var inode_blks: map<Ino, seq<seq<byte>>>;

    // inodes, block_used, and data_block are basically just the data in the
    // journal (except block_used additionally has inode owners)

    // encoded inodes on disk
    ghost var inodes: map<Ino, Inode.Inode>;
    // allocator state + the inode that owns the block
    ghost var block_used: map<Blkno, Option<Ino>>;
    // on-disk value for all the data blocks
    ghost var data_block: map<Blkno, seq<byte>>;

    var jrnl: Jrnl;
    var balloc: Allocator;

    predicate Valid_basics()
      reads this, jrnl
    {
      && jrnl.Valid()
      && jrnl.kinds == fs_kinds
    }

    predicate Valid_domains()
      reads this
    {
      && (forall bn: Blkno | blkno_ok(bn) :: bn in block_used && bn in data_block)
      && (forall ino: Ino | ino_ok(ino) :: ino in inodes && ino in inode_blks && ino in data)
    }

    static lemma blkno_bit_inbounds(jrnl: Jrnl)
      requires jrnl.Valid()
      requires jrnl.kinds == fs_kinds
      ensures forall bn :: blkno_ok(bn) ==> DataBitAddr(bn) in jrnl.data
    {}

    static lemma inode_inbounds(jrnl: Jrnl)
      requires jrnl.Valid()
      requires jrnl.kinds == fs_kinds
      ensures forall ino :: ino_ok(ino) ==> InodeAddr(ino) in jrnl.data
    {
      kind_inode_size();
      forall ino : Ino | ino_ok(ino)
        ensures InodeAddr(ino).blkno == InodeBlk
      {
      }
    }

    predicate Valid_block_used()
      requires Valid_basics()
      reads this, jrnl
    {
      blkno_bit_inbounds(jrnl);
      && (forall bn | bn in block_used ::
        && blkno_ok(bn)
        && jrnl.data[DataBitAddr(bn)] == ObjBit(block_used[bn].Some?))
    }

    predicate Valid_data_block()
      requires Valid_basics()
      reads this, jrnl
    {
      && (forall bn | bn in data_block ::
        && blkno_ok(bn)
        && jrnl.data[DataBlk(bn)] == ObjData(data_block[bn])
        && |data_block[bn]| == 4096)
    }

    predicate Valid_inodes()
      requires Valid_basics()
      reads this, jrnl
    {
      inode_inbounds(jrnl);
      && (forall ino: Ino | ino in inodes ::
        var i2 := inodes[ino];
        && ino_ok(ino)
        && Inode.Valid(i2)
        && jrnl.data[InodeAddr(ino)] == ObjData(Inode.enc(i2))
        && (forall bn | bn in i2.blks ::
          && bn in block_used
          && block_used[bn] == Some(ino))
        )
    }

    predicate inode_blks_match(ino: Ino)
      reads this
      requires Valid_domains()
      requires ino_ok(ino)
    {
      var i3 := inodes[ino];
      && |inode_blks[ino]| == |i3.blks|
      && (forall blk | blk in inode_blks[ino] :: |blk| == 4096)
      && (forall k: nat | k < |i3.blks| ::
        && i3.blks[k] in data_block
        && inode_blks[ino][k] == data_block[i3.blks[k]])
    }

    predicate Valid_data()
      requires Valid_basics()
      requires Valid_domains()
      requires Valid_inodes()
      reads this, jrnl
    {
      && (forall ino: Ino | ino in inodes ::
         && inodes[ino].sz as nat == |data[ino]|
         && inode_blks_match(ino)
         && data[ino] == if inodes[ino].sz as nat % 4096 == 0
                        then C.concat(inode_blks[ino])
                        else C.concat(C.without_last(inode_blks[ino])) +
                             C.last(inode_blks[ino])[..inodes[ino].sz as nat % 4096]
        )
    }

    lemma data_block_val(ino: Ino, k: nat)
      requires && Valid_basics() && Valid_domains() && Valid_inodes() && Valid_data()
      requires ino_ok(ino)
      requires (k+1)*4096 <= |data[ino]|
      ensures inode_blks[ino][k] == data[ino][k*4096..(k+1)*4096]
    {
      if inodes[ino].sz as nat % 4096 == 0 {
        C.concat_homogeneous_one_list(inode_blks[ino], k, 4096);
      } else {
        C.concat_homogeneous_one_list(C.without_last(inode_blks[ino]), k, 4096);
      }
    }

    lemma data_block_val_last(ino: Ino)
      requires && Valid_basics() && Valid_domains() && Valid_inodes() && Valid_data()
      requires ino_ok(ino)
      requires 0 < |inodes[ino].blks|
      ensures C.last(inode_blks[ino])[..inodes[ino].sz as nat % 4096] ==
              data[ino][inodes[ino].sz as nat / 4096 * 4096..]
    {}

    predicate Valid()
      reads this, balloc, jrnl
    {
      && Valid_basics()
      && Valid_domains()

      && this.Valid_block_used()
      && this.Valid_data_block()
      && this.Valid_inodes()
      && this.Valid_data()

      && this.balloc.max == 4095*8
      && this.balloc.Valid()
    }

    constructor Init(d: Disk)
      ensures Valid()
    {
      var jrnl := NewJrnl(d, fs_kinds);
      this.jrnl := jrnl;
      var balloc := NewAllocator(4095*8);
      this.balloc := balloc;

      this.data := map ino: Ino | ino_ok(ino) :: [];
      this.inodes := map ino: Ino | ino_ok(ino) :: Inode.zero;
      this.inode_blks := map ino: Ino | ino_ok(ino) :: [];
      Inode.zero_encoding();
      this.block_used := map bn: uint64 |
        blkno_ok(bn) :: None;
      this.data_block := map bn: uint64 |
        blkno_ok(bn) :: zeroObject(KindBlock).bs;
      new;
      assert Valid_inodes();
    }

    // full block append
    static predicate can_inode_append(i: Inode.Inode, bn: Blkno)
    {
      && Inode.Valid(i)
      && blkno_ok(bn)
      && i.sz < 15*4096
    }

    static function method inode_append(i: Inode.Inode, bn: Blkno): (i':Inode.Inode)
    requires can_inode_append(i, bn)
    {
      Inode.Mk(i.sz + 4096, i.blks + [bn])
    }

    static lemma after_copy_to(bs: seq<byte>, off: nat, data: seq<byte>)
      requires off + |data| <= |bs|
      ensures (bs[..off] + data + bs[off+|data|..])[off..off+|data|] == data
    {}

    method Alloc(txn: Txn) returns (ok:bool, bn:Blkno)
      modifies balloc
      requires txn.jrnl == this.jrnl
      requires Valid() ensures Valid()
      ensures ok ==>
        (&& bn != 0
        && bn-1 < 4095*8
        && blkno_ok(bn)
        && block_used[bn].None?
        )
    {
      bn := balloc.Alloc(); bn := bn + 1;
      var used := txn.ReadBit(DataBitAddr(bn));
      if used {
        ok := false;
        balloc.Free(bn-1);
        return;
      }
      ok := true;
    }

    lemma free_block_unused(bn: Blkno)
      requires Valid()
      requires blkno_ok(bn) && bn != 0 && block_used[bn].None?
      ensures forall ino | ino_ok(ino) :: bn !in inodes[ino].blks
    {}

    method Append(ino: Ino, bs: Bytes) returns (ok:bool)
      modifies this, jrnl, balloc
      requires Valid() ensures Valid()
      requires ino_ok(ino)
      requires bs.Valid()
      requires bs.Len() <= 4096
      ensures ok ==> data == old(data[ino := data[ino] + bs.data])
      ensures !ok ==> data == old(data)
    {
      var txn := jrnl.Begin();

      // check for available space
      var buf := txn.Read(InodeAddr(ino), 128*8);
      var i := Inode.decode_ino(buf, inodes[ino]);
      if sum_overflows(i.sz, bs.Len()) || i.sz + bs.Len() >= 15*4096 {
        ok := false;
        return;
      }
      if bs.Len() == 0 {
        ok := true;
        assert data[ino] + bs.data == data[ino];
        return;
      }

      // is there space in the last block?
      if i.sz + bs.Len() <= Round.roundup64(i.sz, 4096) {
        var blkoff: nat := i.sz as nat/4096;
        assert blkoff < |i.blks|;
        var blk := get_inode_blk(txn, ino, i, blkoff);
        blk.CopyTo(i.sz % 4096, bs);
        var bn := i.blks[blkoff];
        txn.Write(DataBlk(bn), blk);
        data_block := data_block[bn := blk.data];
        inode_blks := inode_blks[ino := inode_blks[ino][blkoff:=blk.data]];

        var i' := Inode.Mk(i.sz + bs.Len(), i.blks);
        var buf' := Inode.encode_ino(i');
        txn.Write(InodeAddr(ino), buf');
        inodes := inodes[ino:=i'];

        data := data[ino := data[ino] + bs.data];

        assert Valid_data_block();
        assert Valid_inodes();
        assert inode_blks_match(ino);
        assert forall ino: Ino | ino_ok(ino) :: inode_blks_match(ino);
        assume false;
        assert Valid_data();

        return;
      }

      assume false;

      // allocate and validate
      var alloc_ok, bn := Alloc(txn);
      if !alloc_ok {
        ok := false;
        return;
      }
      free_block_unused(bn);

      // mark bn in-use now
      block_used := block_used[bn:=Some(ino)];
      txn.WriteBit(DataBitAddr(bn), true);

      var i' := inode_append(i, bn);
      C.unique_extend(i.blks, bn);
      assert Inode.Valid(i');
      i := i';
      var buf' := Inode.encode_ino(i);
      txn.Write(InodeAddr(ino), buf');
      inodes := inodes[ino:=i];

      txn.Write(DataBlk(bn), bs);
      data_block := data_block[bn:=bs.data];
      assert bn in data_block;

      C.concat_app1(inode_blks[ino], bs.data);
      inode_blks := inode_blks[ino := inode_blks[ino] + [bs.data]];
      data := data[ino:=data[ino] + bs.data];

      assert inode_blks_match(ino);

      assert this.Valid_block_used();
      assert this.Valid_data_block();
      assert this.Valid_inodes();
      assert this.Valid_data();

      ok := true;
      var _ := txn.Commit();
    }

    method Size(ino: Ino) returns (sz: uint64)
      requires Valid() ensures Valid()
      requires ino_ok(ino)
      ensures sz as nat == |data[ino]|
    {
      var txn := jrnl.Begin();
      kind_inode_size();
      var buf := txn.Read(InodeAddr(ino), 128*8);
      var i := Inode.decode_ino(buf, inodes[ino]);
      sz := i.sz;
      var _ := txn.Commit();
    }

    method get_inode_blk(txn: Txn, ghost ino: Ino, i: Inode.Inode, blkoff: nat)
      returns (bs: Bytes)
      modifies {}
      requires Valid()
      requires
      && this.jrnl == txn.jrnl
      && ino_ok(ino)
      && i == inodes[ino]
      requires blkoff * 4096 < inodes[ino].sz as nat
      ensures fresh(bs)
      ensures
      && |bs.data| == 4096
      && if i.sz % 4096 == 0 || blkoff < |i.blks|-1
      then bs.data == data[ino][blkoff * 4096..blkoff * 4096 + 4096]
      else (blkoff == |i.blks|-1 && bs.data[..i.sz as nat % 4096] == data[ino][blkoff * 4096..])
    {
      assert blkoff as nat < |inodes[ino].blks|;
      var bn := i.blks[blkoff];
      bs := txn.Read(DataBlk(bn), 4096*8);
      ghost var blk := bs.data;
      assert blk == inode_blks[ino][blkoff];
      if i.sz % 4096 == 0 {
          data_block_val(ino, blkoff);
      } else {
        if blkoff < |i.blks|-1 {
          data_block_val(ino, blkoff);
        } else {
          data_block_val_last(ino);
        }
      }
    }

    method Get(ino: Ino, off: uint64, len: uint64)
      returns (data: Bytes, ok: bool)
      modifies {}
      requires off % 4096 == 0 && len <= 4096
      requires ino_ok(ino)
      requires Valid() ensures Valid()
      // already guaranteed by modifies clause
      ensures data == old(data)
      ensures ok ==> && fresh(data)
                    && (off as nat + len as nat) <= |this.data[ino]|
                    && data.data == this.data[ino][off as nat..(off+len) as nat]
    {
      var txn := jrnl.Begin();
      kind_inode_size();
      var buf := txn.Read(InodeAddr(ino), 128*8);
      var i := Inode.decode_ino(buf, inodes[ino]);
      if sum_overflows(off, len) || off+len > i.sz {
        ok := false;
        data := NewBytes(0);
        return;
      }

      ok := true;
      if len == 0 {
        data := NewBytes(0);
        assert this.data[ino][off as nat..(off+len) as nat] == [];
        return;
      }
      assert (off as nat + len as nat) <= |this.data[ino]|;
      assert 0 < len <= 4096;

      var blkoff: nat := off as nat / 4096;
      data := get_inode_blk(txn, ino, i, blkoff);
      data.Subslice(0, len);
      assert blkoff * 4096 == off as nat;

      // FIXME: the remaining proof is hard but doable for Dafny
      assume false;

      var _ := txn.Commit();
    }
  }
}
