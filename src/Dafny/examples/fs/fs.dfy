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

    lemma inode_in_dom(ino: Ino)
      requires ino_ok(ino)
      requires Valid_domains()
      ensures
      && ino in inodes
      && ino in inode_blks
    {}

    static predicate Valid_jrnl_to_block_used(jrnl: Jrnl, block_used: map<Blkno, Option<Ino>>)
      reads jrnl
      requires blkno_dom(block_used)
      requires Valid_basics(jrnl)
    {
      blkno_bit_inbounds(jrnl);
      && (forall bn | blkno_ok(bn) ::
        && jrnl.data[DataBitAddr(bn)] == ObjBit(block_used[bn].Some?))
    }

    static predicate Valid_jrnl_to_data_block(jrnl: Jrnl, data_block: map<Blkno, Block>)
      reads jrnl
      requires blkno_dom(data_block)
      requires Valid_basics(jrnl)
    {
      && (forall bn | blkno_ok(bn) ::
        datablk_inbounds(jrnl, bn);
        && jrnl.data[DataBlk(bn)] == ObjData(data_block[bn]))
    }

    static predicate Valid_data_block(data_block: map<Blkno, Block>)
    {
      forall bn | bn in data_block :: is_block(data_block[bn])
    }

    static predicate Valid_jrnl_to_inodes(jrnl: Jrnl, inodes: map<Ino, Inode.Inode>)
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
      forall ino: Ino | ino in inodes :: Inode.Valid(inodes[ino])
    }

    static protected predicate Valid_inodes_to_block_used(inodes: map<Ino, Inode.Inode>, block_used: map<Blkno, Option<Ino>>)
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

    // inode i encodes blks, using data_block to lookup indirect references
    static predicate inode_blks_match(i: Inode.Inode, d: InodeData, data_block: map<Blkno, Block>)
    {
      && i.sz as nat == d.sz
      && |d.blks| == |i.blks|
      && InodeData_Valid(d)
      && (forall k: nat | k < |i.blks| ::
        && i.blks[k] in data_block
        && d.blks[k] == data_block[i.blks[k]])
    }

    static predicate Valid_inode_blks_match(
      inodes: map<Ino, Inode.Inode>,
      inode_blks: map<Ino, InodeData>,
      data_block: map<Blkno, Block>)
      requires ino_dom(inodes)
      requires ino_dom(inode_blks)
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

    protected predicate Valid_jrnl_to_all()
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

    function Repr(): set<object>
    {
      {this, balloc, jrnl}
    }

    predicate Valid()
      reads Repr()
    {
      && Valid_basics(jrnl)
      && Valid_domains()

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

    static predicate is_alloc_bn(bn: Blkno)
    {
      && bn != 0
      && bn-1 < 4095*8
      && blkno_ok(bn)
    }

    method Alloc(txn: Txn) returns (ok:bool, bn:Blkno)
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
    }

    lemma free_block_unused(bn: Blkno)
      requires Valid()
      requires blkno_ok(bn) && bn != 0 && block_used[bn].None?
      ensures forall ino | ino_ok(ino) :: bn !in inodes[ino].blks
    {}

    method writeDataBlock(txn: Txn, bn: Blkno, blk: Bytes,
      ghost ino: Ino, ghost blkoff: nat)
      modifies this, jrnl
      requires Valid_jrnl_to_all() ensures Valid_jrnl_to_all()
      requires txn.jrnl == jrnl
      requires blkno_ok(bn)
      requires is_block(blk.data)
      requires ino_ok(ino)
      requires blkoff < |inode_blks[ino].blks|
      requires Inodes_all_Valid(inodes)
      ensures
      && inodes == old(inodes)
      && block_used == old(block_used)
      && data_block == old(data_block)[bn := blk.data]
      && inode_blks ==
        old(var d0 := inode_blks[ino];
            var d' := d0.(blks := d0.blks[blkoff:=blk.data]);
            inode_blks[ino:=d'])
    {
      datablk_inbounds(jrnl, bn);
      txn.Write(DataBlk(bn), blk);
      data_block := data_block[bn := blk.data];
      ghost var d0 := inode_blks[ino];
      ghost var d' := d0.(blks := d0.blks[blkoff:=blk.data]);
      inode_blks := inode_blks[ino:=d'];
    }

    method writeInodeSz(txn: Txn, ino: Ino, ghost i: Inode.Inode, i': Inode.Inode)
      modifies this, jrnl
      requires Valid_jrnl_to_all() ensures Valid_jrnl_to_all()
      requires txn.jrnl == jrnl
      requires is_inode(ino, i)
      requires i'.blks == i.blks
      requires Inode.Valid(i')
      requires Inodes_all_Valid(inodes)
      ensures Inodes_all_Valid(inodes)
      ensures is_inode(ino, i')
      ensures
      && inodes == old(inodes)[ino:=i']
      && block_used == old(block_used)
      && data_block == old(data_block)
      && inode_blks == old(inode_blks[ino:=inode_blks[ino].(sz := i'.sz as nat)])
    {
      inode_inbounds(jrnl, ino);
      var buf' := Inode.encode_ino(i');
      txn.Write(InodeAddr(ino), buf');
      inodes := inodes[ino:=i'];
      inode_blks := inode_blks[ino:=inode_blks[ino].(sz := i'.sz as nat)];
    }

    static lemma inode_blks_match_change_1(
      i: Inode.Inode, d: InodeData, data_block: map<Blkno, seq<byte>>,
      i': Inode.Inode, bn: Blkno, blkoff: nat, bs: seq<byte>)
      requires inode_blks_match(i, d, data_block)
      requires blkoff < |i.blks|
      requires |bs| == 4096
      requires Inode.Valid(i)
      requires Inode.Valid(i')
      requires i'.blks == i.blks
      requires bn in data_block
      requires i.blks[blkoff] == bn
      ensures inode_blks_match(i', InodeData(i'.sz as nat, d.blks[blkoff:=bs]), data_block[bn := bs])
    {
      Inode.reveal_blks_unique();
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
    {}

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
      inode_inbounds(jrnl, ino);
      var buf := txn.Read(InodeAddr(ino), 128*8);
      i := Inode.decode_ino(buf, inodes[ino]);
    }

    method allocateTo(txn: Txn, ino: Ino, ghost i: Inode.Inode) returns (ok: bool, bn:Blkno)
      modifies this, jrnl, balloc
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
      ok, bn := Alloc(txn);
      if !ok {
        return;
      }
      free_block_unused(bn);

      blkno_bit_inbounds(jrnl);
      block_used := block_used[bn:=Some(ino)];
      txn.WriteBit(DataBitAddr(bn), true);
      return;
    }

    // freeing is not as simple as allocation: to maintain invariants, we need
    // to simultaneously free a block and remove it from the blocks of an inode
    //
    // TODO: need to track is_alloc_bn for all blks in an inode, not the weaker
    // != 0 property being tracked by Inode.Valid or blkno_ok from
    // Valid_inodes_to_block_used

    method Append(ino: Ino, bs: Bytes) returns (ok:bool)
      modifies this, jrnl, balloc
      requires Valid() ensures Valid()
      requires ino_ok(ino)
      requires bs.Valid()
      requires bs.Len() <= 4096
      // TODO: write ensures in terms of inode_blks
    {
      inode_in_dom(ino);
      ghost var this_ino := ino;
      var txn := jrnl.Begin();

      // check for available space
      var i := getInode(txn, ino);
      if sum_overflows(i.sz, bs.Len()) || i.sz + bs.Len() >= 15*4096 {
        ok := false;
        return;
      }
      if bs.Len() == 0 {
        ok := true;
        return;
      }

      // is there space in the last block?
      if i.sz + bs.Len() <= Round.roundup64(i.sz, 4096) {
        Round.roundup_distance(i.sz as nat, 4096);

        var blkoff: nat := i.sz as nat/4096;
        assert blkoff == |i.blks|-1;
        var blk := getInodeBlk(txn, ino, i, blkoff);
        blk.CopyTo(i.sz % 4096, bs);
        assert blk.data[..i.sz % 4096] == C.last(inode_blks[ino].blks)[..i.sz % 4096];
        var bn := i.blks[blkoff];
        writeDataBlock(txn, bn, blk, ino, blkoff);

        var i' := i.(sz := i.sz + bs.Len());
        Inode.Valid_sz_bound(i);
        assert Inode.Valid(i');
        writeInodeSz(txn, ino, i, i');
        var _ := txn.Commit();
        ok := true;

        inode_in_dom(ino);
        inodes := inodes[ino:=i'];

        assert Inodes_all_Valid(inodes);
        assert Valid_inodes_to_block_used(inodes, block_used);
        assert Valid_inodes();
        inode_blks_match_change_1(i, old(inode_blks[ino]), old(data_block),
          i', bn, blkoff, blk.data);

        forall ino | ino_ok(ino)
          ensures inode_blks_match(inodes[ino], inode_blks[ino], data_block)
        {
          inode_blks_match_change_other(ino, old(inode_blks[ino]),
            old(inodes), old(data_block), old(block_used),
            this_ino, bn, blk.data);
        }
        assert Valid_inode_blks_match(inodes, inode_blks, data_block);

        return;
      }

      // allocate and validate
      var alloc_ok, bn := allocateTo(txn, ino, i);
      if !alloc_ok {
        ok := false;
        return;
      }
      assume false;

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

      C.concat_app1(inode_blks[ino].blks, bs.data);
      ghost var d0 := inode_blks[ino];
      ghost var d' := d0.(blks := d0.blks + [bs.data]);
      inode_blks := inode_blks[ino := d'];

      assert inode_blks_match(inodes[ino], inode_blks[ino], data_block);

      assert Valid_jrnl_to_block_used(jrnl, block_used);
      assert Valid_jrnl_to_data_block(jrnl, data_block);
      assert this.Valid_inodes();

      assume false;

      ok := true;
      var _ := txn.Commit();
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
      requires Valid()
      requires
      && this.jrnl == txn.jrnl
      && is_inode(ino, i)
      requires blkoff * 4096 < i.sz as nat
      ensures fresh(bs)
      ensures
      && is_block(bs.data)
      && bs.data == inode_blks[ino].blks[blkoff]
    {
      assert blkoff as nat < |inodes[ino].blks|;
      var bn := i.blks[blkoff];
      datablk_inbounds(jrnl, bn);
      bs := txn.Read(DataBlk(bn), 4096*8);
    }
  }
}
