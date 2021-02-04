include "../../util/marshal.i.dfy"
include "../../jrnl/jrnl.s.dfy"
include "kinds.dfy"
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
  import opened FsKinds
  import opened Marshal

  datatype Option<T> = Some(x:T) | None

  type Block = seq<byte>
  predicate is_block(b: Block) { |b| == 4096 }
  datatype InodeData = InodeData(sz: nat, blks: seq<Block>)
  predicate InodeData_Valid(d: InodeData)
  {
    && |d.blks| <= 15
    && |d.blks| == Round.div_roundup_alt(d.sz, 4096)
    && (forall blk | blk in d.blks :: is_block(blk))
  }

  predicate blkno_dom<T>(m: map<Blkno, T>)
  {
    forall bn: Blkno :: blkno_ok(bn) <==> bn in m
  }

  predicate ino_dom<T>(m: map<Ino, T>)
  {
    forall ino: Ino :: ino_ok(ino) <==> ino in m
  }

  predicate Valid_inode_blks(inode_blks: map<Ino, InodeData>)
    requires ino_dom(inode_blks)
  {
    forall ino | ino_ok(ino) :: InodeData_Valid(inode_blks[ino])
  }

  class Filesys
  {

    // block-based inodes
    ghost var inode_blks: map<Ino, InodeData>;

    // inodes, block_used, and data_block are basically just the data in the
    // journal (except block_used additionally has inode owners)

    // encoded inodes on disk
    ghost var inodes: map<Ino, Inode.Inode>;
    // allocator state + the inode that owns the block
    ghost var block_used: map<Blkno, Option<Ino>>;
    // on-disk value for all the data blocks
    ghost var data_block: map<Blkno, Block>;

    const jrnl: Jrnl;
    const balloc: Allocator;

    static predicate Valid_basics(jrnl: Jrnl)
      reads jrnl
    {
      && jrnl.Valid()
      && jrnl.kinds == fs_kinds
    }

    predicate Valid_domains()
      reads this
    {
      && blkno_dom(block_used)
      && blkno_dom(data_block)
      && ino_dom(inodes)
      && ino_dom(inode_blks)
    }

    static predicate {:opaque} Valid_jrnl_to_block_used(jrnl: Jrnl, block_used: map<Blkno, Option<Ino>>)
      reads jrnl
      requires blkno_dom(block_used)
      requires Valid_basics(jrnl)
    {
      blkno_bit_inbounds(jrnl);
      && (forall bn | blkno_ok(bn) ::
        && jrnl.data[DataBitAddr(bn)] == ObjBit(block_used[bn].Some?))
    }

    static predicate {:opaque} Valid_jrnl_to_data_block(jrnl: Jrnl, data_block: map<Blkno, Block>)
      reads jrnl
      requires blkno_dom(data_block)
      requires Valid_basics(jrnl)
    {
      && (forall bn | blkno_ok(bn) ::
        datablk_inbounds(jrnl, bn);
        && jrnl.data[DataBlk(bn)] == ObjData(data_block[bn]))
    }

    static predicate {:opaque} Valid_jrnl_to_inodes(jrnl: Jrnl, inodes: map<Ino, Inode.Inode>)
      reads jrnl
      requires ino_dom(inodes)
      requires Valid_basics(jrnl)
    {
      && (forall ino: Ino | ino_ok(ino) ::
        inode_inbounds(jrnl, ino);
        && jrnl.data[InodeAddr(ino)] == ObjData(Inode.enc(inodes[ino])))
    }

    static predicate Inodes_all_Valid(inodes: map<Ino, Inode.Inode>)
    {
      forall ino: Ino | ino in inodes :: inodes[ino].Valid()
    }

    static predicate {:opaque} Valid_inodes_to_block_used(inodes: map<Ino, Inode.Inode>, block_used: map<Blkno, Option<Ino>>)
      requires blkno_dom(block_used)
    {
      && (forall ino: Ino | ino in inodes ::
        && (forall bn | bn in inodes[ino].blks ::
          && blkno_ok(bn)
          && block_used[bn] == Some(ino))
        )
    }

    predicate Valid_inodes()
      requires Valid_domains()
      reads this
    {
      && Inodes_all_Valid(inodes)
      && Valid_inodes_to_block_used(inodes, block_used)
    }

    static predicate {:opaque} blks_match?(blk_offs: seq<Blkno>, blks: seq<Block>, data_block: map<Blkno, Block>)
      requires |blk_offs| == |blks|
      requires blkno_dom(data_block)
    {
      forall k: nat | k < |blk_offs| ::
        && blkno_ok(blk_offs[k])
        && blks[k] == data_block[blk_offs[k]]
    }

    // inode i encodes blks, using data_block to lookup indirect references
    static predicate inode_blks_match(i: Inode.Inode, d: InodeData, data_block: map<Blkno, Block>)
    {
      && i.sz as nat == d.sz
      && |d.blks| == |i.blks|
      && InodeData_Valid(d)
      && blkno_dom(data_block)
      && blks_match?(i.blks, d.blks, data_block)
    }

    static predicate Valid_inode_blks_match(
      inodes: map<Ino, Inode.Inode>,
      inode_blks: map<Ino, InodeData>,
      data_block: map<Blkno, Block>)
      requires ino_dom(inodes)
      requires ino_dom(inode_blks)
      requires blkno_dom(data_block)
    {
      && (forall ino: Ino | ino_ok(ino) ::
         && inode_blks_match(inodes[ino], inode_blks[ino], data_block))
    }

    predicate Valid_balloc()
      reads this, balloc
    {
      && this.balloc.max == 4095*8
      && this.balloc.Valid()
    }

    predicate Valid_jrnl_to_all()
      reads this, jrnl
    {
      && Valid_basics(jrnl)
      && Valid_domains()
      && Valid_jrnl_to_block_used(jrnl, block_used)
      && Valid_jrnl_to_data_block(jrnl, data_block)
      && Valid_jrnl_to_inodes(jrnl, inodes)
    }

    predicate Valid_data()
      reads this
      requires Valid_domains()
    {
      && Valid_inode_blks_match(inodes, inode_blks, data_block)
    }

    lemma inode_blks_sz(ino: Ino)
      requires Valid_domains()
      requires Valid_data()
      requires ino_ok(ino)
      ensures inodes[ino].sz as nat == inode_blks[ino].sz
    {
      assert inode_blks_match(inodes[ino], inode_blks[ino], data_block);
    }

    function Repr(): set<object>
    {
      {this, balloc, jrnl}
    }

    static predicate Valid_data_block(data_block: map<Blkno, Block>)
    {
      forall bn | bn in data_block :: is_block(data_block[bn])
    }

    predicate Valid()
      reads Repr()
    {
      && Valid_data_block(data_block)
      && Valid_jrnl_to_all()
      && this.Valid_inodes()
      && this.Valid_data()

      && this.Valid_balloc()
    }

    lemma Valid_inode_data()
      requires Valid_domains()
      requires Valid_data()
      ensures Valid_inode_blks(inode_blks)
    {}

    constructor Init(d: Disk)
      ensures Valid()
      ensures inode_blks == map ino | ino_ok(ino) :: InodeData(0, [])
    {
      var jrnl := NewJrnl(d, fs_kinds);
      this.jrnl := jrnl;
      var balloc := NewAllocator(4095*8);
      this.balloc := balloc;

      this.inodes := map ino: Ino | ino_ok(ino) :: Inode.zero;
      this.inode_blks := map ino: Ino | ino_ok(ino) :: InodeData(0, []);
      Inode.zero_encoding();
      this.block_used := map bn: uint64 | blkno_ok(bn) :: None;
      this.data_block := map bn: uint64 | blkno_ok(bn) :: zeroObject(KindBlock).bs;
      new;
      jrnl.reveal_Valid();
      reveal_Valid_inodes_to_block_used();
      reveal_addrsForKinds();

      reveal_Valid_jrnl_to_block_used();
      reveal_Valid_jrnl_to_data_block();
      reveal_Valid_jrnl_to_inodes();
      reveal_blks_match?();
      assert Valid_inodes();
    }

    // Recovery is needed for the file-system to recover its in-memory allocator
    // state. Due to the use of translation validation (that is, we don't prove
    // the allocator has the right free elements but check the on-disk value) we
    // don't have to re-establish any invariant here, but without this code on
    // recovery the allocator will give out used addresses and fail in practice.
    constructor Recover(jrnl_: Jrnl)
      // not allowed to modify jrnl so can't break any invariants
      modifies {}
      requires Valid_basics(jrnl_)
      ensures this.jrnl == jrnl_
    {
      var balloc := NewAllocator(4095*8);

      var txn := jrnl_.Begin();
      blkno_bit_inbounds(jrnl_);
      var bn: Blkno := 1;
      while bn < 4095*8
        invariant txn.jrnl == jrnl_
        invariant Valid_basics(jrnl_)
        invariant balloc.Valid()
        invariant 1 <= bn as nat <= 4095*8
      {
        var used := txn.ReadBit(DataBitAddr(bn));
        if used {
          balloc.MarkUsed(bn);
        }
        bn := bn + 1;
      }

      this.jrnl := jrnl_;
      this.balloc := balloc;
    }

    // full block append
    static predicate can_inode_append(i: Inode.Inode, bn: Blkno)
    {
      && i.Valid()
      && blkno_ok(bn)
      && i.sz < 15*4096
    }

    static function method inode_append(i: Inode.Inode, bn: Blkno): (i':Inode.Inode)
    requires can_inode_append(i, bn)
    {
      Inode.Mk(i.sz + 4096, i.blks + [bn])
    }

    static predicate is_alloc_bn(bn: Blkno)
    {
      && bn != 0
      && bn-1 < 4095*8
      && blkno_ok(bn)
    }

    method allocBlkno(txn: Txn) returns (ok:bool, bn:Blkno)
      modifies balloc
      requires txn.jrnl == this.jrnl
      requires Valid() ensures Valid()
      ensures ok ==>
        (&& is_alloc_bn(bn)
         && block_used[bn].None?
        )
    {
      bn := balloc.Alloc(); bn := bn + 1;
      blkno_bit_inbounds(jrnl);
      var used := txn.ReadBit(DataBitAddr(bn));
      if used {
        ok := false;
        balloc.Free(bn-1);
        return;
      }
      ok := true;
      reveal_Valid_jrnl_to_block_used();
    }

    lemma free_block_unused(bn: Blkno)
      requires Valid()
      requires blkno_ok(bn) && bn != 0 && block_used[bn].None?
      ensures forall ino | ino_ok(ino) :: bn !in inodes[ino].blks
    {
      reveal_Valid_inodes_to_block_used();
    }

    method writeDataBlock(txn: Txn, bn: Blkno, blk: Bytes,
      ghost ino: Ino, ghost blkoff: nat)
      modifies this, jrnl
      requires Valid() ensures Valid()
      requires txn.jrnl == jrnl
      requires is_block(blk.data)
      requires ino_ok(ino)
      requires blkoff < |inode_blks[ino].blks|
      requires inodes[ino].blks[blkoff] == bn
      ensures
      && inodes == old(inodes)
      && block_used == old(block_used)
      && data_block == old(data_block)[bn := blk.data]
      && inode_blks ==
        old(var d0 := inode_blks[ino];
            var d' := d0.(blks := d0.blks[blkoff:=blk.data]);
            inode_blks[ino:=d'])
    {
      assert inode_blks_match(inodes[ino], inode_blks[ino], data_block);
      reveal_blks_match?();
      datablk_inbounds(jrnl, bn);
      txn.Write(DataBlk(bn), blk);
      data_block := data_block[bn := blk.data];
      ghost var d0 := inode_blks[ino];
      ghost var d' := d0.(blks := d0.blks[blkoff:=blk.data]);
      inode_blks := inode_blks[ino:=d'];

      ghost var i := inodes[ino];
      inode_blks_match_change_1(i, d0, old(data_block), i, bn, blkoff, blk.data);

      Filesys.reveal_Valid_inodes_to_block_used();
      assert Inodes_all_Valid(inodes);
      ghost var this_ino := ino;
      forall ino | ino_ok(ino)
        ensures inode_blks_match(inodes[ino], inode_blks[ino], data_block)
      {
        inode_blks_match_change_other(ino, old(inode_blks[ino]),
          old(inodes), old(data_block), old(block_used),
          this_ino, bn, blk.data);
      }

      reveal_Valid_jrnl_to_block_used();
      reveal_Valid_jrnl_to_data_block();
      reveal_Valid_jrnl_to_inodes();
    }

    method writeInode(txn: Txn, ino: Ino, ghost i: Inode.Inode, i': Inode.Inode)
      modifies this, jrnl
      requires Valid_jrnl_to_all() ensures Valid_jrnl_to_all()
      requires Inodes_all_Valid(inodes) ensures Inodes_all_Valid(inodes)
      requires txn.jrnl == jrnl
      requires is_inode(ino, i)
      requires i'.Valid()
      ensures is_inode(ino, i')
      ensures inodes == old(inodes)[ino:=i']
      ensures block_used == old(block_used)
      ensures data_block == old(data_block)
      ensures inode_blks == old(inode_blks)
    {
      inode_inbounds(jrnl, ino);
      var buf' := Inode.encode_ino(i');
      txn.Write(InodeAddr(ino), buf');
      inodes := inodes[ino:=i'];

      reveal_Valid_jrnl_to_block_used();
      reveal_Valid_jrnl_to_data_block();
      reveal_Valid_jrnl_to_inodes();
    }

    method writeInodeSz(txn: Txn, ino: Ino, ghost i: Inode.Inode, i': Inode.Inode)
      modifies this, jrnl
      requires Valid_jrnl_to_all() ensures Valid_jrnl_to_all()
      requires Inodes_all_Valid(inodes) ensures Inodes_all_Valid(inodes)
      requires txn.jrnl == jrnl
      requires is_inode(ino, i)
      requires i'.blks == i.blks
      requires i'.Valid()
      ensures is_inode(ino, i')
      ensures
      && inodes == old(inodes)[ino:=i']
      && block_used == old(block_used)
      && data_block == old(data_block)
      && inode_blks == old(inode_blks[ino:=inode_blks[ino].(sz := i'.sz as nat)])
    {
      writeInode(txn, ino, i, i');
      inode_blks := inode_blks[ino:=inode_blks[ino].(sz := i'.sz as nat)];
    }

    static lemma inode_blks_match_change_1(
      i: Inode.Inode, d: InodeData, data_block: map<Blkno, seq<byte>>,
      i': Inode.Inode, bn: Blkno, blkoff: nat, bs: seq<byte>)
      requires inode_blks_match(i, d, data_block)
      requires blkoff < |i.blks|
      requires |bs| == 4096
      requires i.Valid()
      requires i'.Valid()
      requires i'.blks == i.blks
      requires bn in data_block
      requires i.blks[blkoff] == bn
      ensures inode_blks_match(i', InodeData(i'.sz as nat, d.blks[blkoff:=bs]), data_block[bn := bs])
    {
      Inode.reveal_blks_unique();
      reveal_blks_match?();
    }

    // inode_blks_match is insensitive to changes in blocks owned by other inodes
    static lemma inode_blks_match_change_other(
      ino: Ino, d: InodeData,
      inodes: map<Ino, Inode.Inode>,
      data_block: map<Blkno, seq<byte>>,
      block_used: map<Blkno, Option<Ino>>,
      // stuff that changed in an unrelated inode ino':
      ino': Ino, bn: Blkno, bs: seq<byte>)
      requires && blkno_dom(data_block) && blkno_dom(block_used) && blkno_ok(bn)
      requires && ino_dom(inodes) && ino_ok(ino) && ino_ok(ino')
      requires inode_blks_match(inodes[ino], d, data_block)
      requires Valid_inodes_to_block_used(inodes, block_used)
      requires block_used[bn] == Some(ino')
      ensures ino != ino' ==> inode_blks_match(inodes[ino], d, data_block[bn:=bs])
    {
      reveal_Valid_inodes_to_block_used();
      reveal_blks_match?();
    }

    predicate is_inode(ino: Ino, i: Inode.Inode)
      reads this, jrnl
      requires Valid_basics(jrnl)
      requires Valid_domains()
    {
      && ino_ok(ino)
      && inodes[ino] == i
    }

    method getInode(txn: Txn, ino: Ino) returns (i:Inode.Inode)
      modifies {}
      requires Valid()
      requires ino_ok(ino)
      requires txn.jrnl == jrnl
      ensures is_inode(ino, i)
    {
      reveal_Valid_jrnl_to_inodes();
      inode_inbounds(jrnl, ino);
      var buf := txn.Read(InodeAddr(ino), 128*8);
      i := Inode.decode_ino(buf, inodes[ino]);
    }

    method allocateTo(txn: Txn, ino: Ino, ghost i: Inode.Inode) returns (ok: bool, bn:Blkno)
      modifies Repr()
      requires Valid() ensures Valid()
      requires txn.jrnl == jrnl
      requires is_inode(ino, i)
      ensures inode_blks == old(inode_blks)
      ensures inodes == old(inodes)
      ensures !ok ==> block_used == old(block_used)
      ensures data_block == old(data_block)
      ensures ok ==> forall ino | ino_ok(ino) :: bn !in inodes[ino].blks
      ensures ok ==> block_used == old(block_used[bn:=Some(ino)])
      ensures ok ==> is_alloc_bn(bn)
    {
      ok, bn := allocBlkno(txn);
      if !ok {
        return;
      }
      free_block_unused(bn);

      blkno_bit_inbounds(jrnl);
      block_used := block_used[bn:=Some(ino)];
      txn.WriteBit(DataBitAddr(bn), true);
      reveal_Valid_inodes_to_block_used();
      reveal_Valid_jrnl_to_block_used();
      reveal_Valid_jrnl_to_data_block();
      reveal_Valid_jrnl_to_inodes();
      return;
    }

    // freeing is not as simple as allocation: to maintain invariants, we need
    // to simultaneously free a block and remove it from the blocks of an inode
    //
    // TODO: need to track is_alloc_bn for all blks in an inode, not the weaker
    // != 0 property being tracked by Inode.Valid or blkno_ok from
    // Valid_inodes_to_block_used

    method growInode(txn: Txn, ino: Ino, i: Inode.Inode) returns (ok:bool, bn: Blkno)
      modifies Repr()
      requires Valid() ensures Valid()
      requires txn.jrnl == jrnl
      requires is_inode(ino, i)
      requires i.sz <= 14*4096
      requires i.sz % 4096 == 0
      ensures data_block == old(data_block)
      ensures ok ==> blkno_ok(bn)
      ensures ok ==> block_used[bn] == Some(ino)
      ensures ok ==> inode_blks ==
        old(var d0 := inode_blks[ino];
            var d' := InodeData(d0.sz + 4096, d0.blks + [data_block[bn]]);
            inode_blks[ino := d'])
      ensures !ok ==> inode_blks == old(inode_blks)
      ensures ok ==> is_inode(ino, inode_append(i, bn))
    {
      ok, bn := allocateTo(txn, ino, i);
      if !ok {
        return;
      }
      ok := true;

      // this is the garbage data we're adding to the inode
      ghost var data := data_block[bn];

      var i' := Filesys.inode_append(i, bn);
      assert i'.Valid() by {
        Inode.reveal_blks_unique();
        C.unique_extend(i.blks, bn);
      }
      writeInode(txn, ino, i, i');

      ghost var d0 := inode_blks[ino];
      ghost var d' := InodeData(d0.sz + 4096, d0.blks + [data]);
      inode_blks := inode_blks[ino:=d'];

      assert inode_blks_match(i', d', data_block) by {
        reveal_blks_match?();
      }
      assert Valid_inodes_to_block_used(inodes, block_used) by {
        reveal_Valid_inodes_to_block_used();
      }

      return;
    }

    method Size(ino: Ino) returns (sz: uint64)
      modifies {}
      requires Valid() ensures Valid()
      requires ino_ok(ino)
      ensures sz as nat == inodes[ino].sz as nat
    {
      var txn := jrnl.Begin();
      var i := getInode(txn, ino);
      sz := i.sz;
      var _ := txn.Commit();
    }

    method getInodeBlk(txn: Txn, ghost ino: Ino, i: Inode.Inode, blkoff: nat)
      returns (bs: Bytes)
      modifies {}
      requires Valid() ensures Valid()
      requires
      && this.jrnl == txn.jrnl
      && is_inode(ino, i)
      requires blkoff * 4096 < i.sz as nat
      ensures fresh(bs)
      ensures
      && is_block(bs.data)
      && bs.data == inode_blks[ino].blks[blkoff]
      && blkno_ok(i.blks[blkoff])
      && block_used[i.blks[blkoff]] == Some(ino)
    {
      assert blkoff as nat < |inodes[ino].blks|;
      var bn := i.blks[blkoff];
      reveal_blks_match?();
      datablk_inbounds(jrnl, bn);
      bs := txn.Read(DataBlk(bn), 4096*8);
      reveal_Valid_inodes_to_block_used();
      reveal_Valid_jrnl_to_data_block();
    }

    lemma inode_sz_no_overflow(ino: Ino, i: Inode.Inode, delta: uint64)
      requires Valid()
      requires is_inode(ino, i)
      requires delta as nat <= 8192
      ensures no_overflow(i.sz as nat, delta as nat)
    {}
  }
}
