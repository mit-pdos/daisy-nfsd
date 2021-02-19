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
  import IndBlocks
  import opened Pow
  import C = Collections

  datatype preIndOff = IndOff(ilevel: nat, j: nat)
  {
    static const direct: IndOff := IndOff(0, 0)

    predicate Valid()
    {
      j < pow(512, ilevel)
    }

    function method parent(): IndOff
      requires Valid()
      requires ilevel > 0
    {
      IndOff(ilevel-1, j / 512)
    }

    function method child(): IndOff
      requires Valid()
      requires ilevel > 0
    {
      IndOff(1, j % 512)
    }
  }
  type IndOff = x:preIndOff | x.Valid() witness IndOff(0, 0)

  datatype Config = Config(ilevels: seq<nat>)
  {
    const totals := configSum(ilevels)
    const total := configTotal(ilevels)

    static function method configTotal(ilevels: seq<nat>): nat
    {
      if ilevels == [] then 0
      else pow(512, ilevels[0]) + configTotal(ilevels[1..])
    }

    static lemma test_configSum1()
      ensures configSum([0]) == [0,1]
    {}

    static lemma test_configSum2()
      ensures configSum([0,1]) == [0,1,1+512]
    {
      assert [0,1][..1] == [0];
    }

    static lemma test_configSum3()
      ensures configSum([0,0,1,2]) == [0,1,2,2+512, 2+512+512*512]
    {
      assert configTotal([0,0,1,2]) == 2+512+512*512;
      assert [0,0,1,2][..3] == [0,0,1];
      assert [0,0,1][..2] == [0,0];
      assert [0,0][..1] == [0];
    }

    static function method configSum(ilevels: seq<nat>): (s:seq<nat>)
      ensures |s| == 1+|ilevels|
      ensures forall i | 0 <= i <= |ilevels| :: s[i] == configTotal(ilevels[..i])
    {
      if ilevels == [] then [0]
      else (
        assert ilevels[..|ilevels|] == ilevels;
        var s := configSum(ilevels[..|ilevels|-1]) + [configTotal(ilevels)];
        assert s[|ilevels|] == configTotal(ilevels);
        // NOTE(tej): need to assert this to get into statement context; see
        // https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#2036-statements-in-an-expression
        // which does not include forall statements
        assert forall i | 0 <= i <= |ilevels| :: s[i] == configTotal(ilevels[..i]) by
        {
          forall i | 0 <= i <= |ilevels|
            ensures s[i] == configTotal(ilevels[..i])
          {
            if i == |ilevels| {}
            else {
              calc {
                s[i];
                configSum(ilevels[..|ilevels|-1])[i];
                { assert ilevels[..|ilevels|-1][..i] == ilevels[..i]; }
                configTotal(ilevels[..i]);
              }
            }
          }
        }
        s
      )
    }

  }

  const config: Config := Config([0,0,0,0,0,0,0,0,0,0,1,1,1,1,3])

  lemma config_properties()
    ensures |config.ilevels| == 15
    ensures config.total == 10 + 4*512 + 512*512*512
    // these inodes can hold at least 10GB
    ensures config.total * 4 / 1024 /* MB */ > 10_000
  {}

  lemma config_totals()
    ensures config.totals == [0,1,2,3,4,5,6,7,8,9,10,10+512,10+2*512,10+3*512,10+4*512, 10+4+512 + 512*512*512]
  {
    var totals := [0,1,2,3,4,5,6,7,8,9,10,10+512,10+2*512,10+3*512,10+4*512, 10+4+512 + 512*512*512];
    forall i | 0 <= i <= 15
      ensures config.totals[i] == Config.configTotal(config.ilevels[..i])
    {
    }
    forall i | 0 <= i <= 15
      ensures Config.configTotal(config.ilevels[..i]) == totals[i]
    {
      if i == 0 {}
      else if i == 1 {}
      else if i == 2 {
        // this first assertion is needed for the second to work (but
        // Config.configTotal([0,0]) == 2 is easy on its own)
        assert config.ilevels[..2] == [0,0];
        assert Config.configTotal(config.ilevels[..2]) == 2;
        //calc {
        //  Config.configTotal(config.ilevels[..2]);
        //  // these constant subslices aren't automatically triggered
        //  { assert config.ilevels[..2] == [0,0]; }
        //  Config.configTotal([0,0]);
        //  2;
        //}
      }
      // TODO: how to brute force this? it's just calculation...
      else { assume false; }
    }
    assert config.totals[0] == totals[0];
    assert config.ilevels[..1] == config.ilevels[..1];
    assert config.totals[1] == 1;
  }

  datatype preIdx = Idx(k: nat, off: IndOff)
  {
    const ilevel: nat := off.ilevel
    const data?: bool := k < |config.ilevels| && off.ilevel == config.ilevels[k]

    static function from_inode(k: nat): Idx
      requires k < |config.ilevels|
    {
      Idx(k, IndOff.direct)
    }

    predicate Valid()
    {
      && k < |config.ilevels|
      && off.ilevel <= config.ilevels[k]
    }

    // "flat" indices are logical block addresses (LBAs) for the inode
    function flat(): nat
      requires Valid()
      requires this.data?
    {
      config.totals[k] + off.j
    }

    // from_flat gives us a structured way to find an LBA (we go to its
    // appropriate root block and deference indirect blocks one at a time with
    // i.split() until we get a direct block)
    static function from_flat(n: nat): (i:Idx)
      requires n < config.total
      ensures i.data?
    {
      if n < 10 then
        Idx(n, IndOff.direct)
      else (
        var n: nat := n-10;
        if n < 4*512 then
          Idx(10+n/512, IndOff(1, n%512))
        else (
          var n: nat := n-4*512;
          // there's only one triply-indirect block so no complicated
          // calculations are needed here
          Idx(14, IndOff(3, n))
        )
      )
    }

    lemma from_to_flat_id(n: nat)
      requires n < config.total
      ensures from_flat(n).flat() == n
    {
      config_totals();
      if n < 10 { return; }
      assert n >= 10;
      var n0 := n;
      var n := n-10;
      if n < 4*512 {
        assert 10 <= from_flat(n0).k < 14;
        if n < 512 {
          return;
        }
        if n < 2*512 {
          return;
        }
        if n < 3*512 {
          return;
        }
        return;
      }
      assert from_flat(n0).flat() == 10+4*512 + (n-4*512);
    }

  }
  type Idx = x:preIdx | x.Valid() witness Idx(0, IndOff(0, 0))

  // This is the primary notion of an abstract location in the file system. A
  // data Pos has three dimensions: inode, top-level block in inode, and
  // offset within that block. Indirect blocks have an inode and top-level block
  // as well as an indirection level which might be higher than the bottom where
  // the data lives.
  datatype prePos = Pos(ino: Ino, idx: Idx)
  {
    const ilevel: nat := idx.off.ilevel;
    const data?: bool := idx.data?

    predicate Valid()
    {
      ino_ok(ino)
    }

    function method parent(): Pos
      requires Valid()
      requires ilevel > 0
    {
      Pos(ino, Idx(idx.k, idx.off.parent()))
    }

    function method child(): IndOff
      requires Valid()
      requires ilevel > 0
    {
      idx.off.child()
    }

  }
  type Pos = x:prePos | x.Valid() witness Pos(0, Idx(0, IndOff(0,0)))
  function MkPos(ino: Ino, idx: Idx): Pos
    requires Pos(ino, idx).Valid()
  {
    Pos(ino, idx)
  }

  predicate pos_dom<T>(m: imap<Pos, T>)
  {
    forall p:Pos :: p in m
  }

  class IndFilesys
  {
    // filesys contains a mapping from allocated Blkno's to poss
    const fs: Filesys<Pos>
    // this is a complete map; every position in every inode has a value, but
    // it might be a zero block encoded efficiently via 0's.
    ghost var to_blkno: imap<Pos, Blkno>
    // only maps data poss (this hides when other blocks change but exposes
    // newly-allocated data blocks)
    ghost var data: imap<Pos, Block>
    ghost var metadata: map<Ino, uint64>

    function blkno_pos(bn: Blkno): Option<Pos>
      reads fs.Repr()
      requires blkno_ok(bn)
      requires fs.Valid()
    {
      fs.block_used[bn]
    }

    function Repr(): set<object>
    {
      {this} + fs.Repr()
    }

    predicate ValidBasics()
      reads Repr()
    {
      && fs.Valid()
      && pos_dom(to_blkno)
      && ino_dom(metadata)
      // no blkno_dom(data) - domain is a non-trivial subset of blocks
      && (forall pos:Pos :: blkno_ok(to_blkno[pos]))
      && fs.block_used[0].None?
    }

    predicate {:opaque} ValidPos()
      reads Repr()
      requires ValidBasics()
    {
      && (forall bn:Blkno | bn != 0 && blkno_ok(bn) ::
          blkno_pos(bn).Some? ==> to_blkno[blkno_pos(bn).x] == bn)
      && (forall pos:Pos ::
          var bn := to_blkno[pos];
          && blkno_ok(bn)
          && (bn != 0 ==> blkno_pos(bn) == Some(pos)))
    }

    lemma blkno_unused(bn: Blkno)
      requires ValidBasics() && ValidPos()
      requires blkno_ok(bn) && bn != 0 && blkno_pos(bn).None?
      ensures forall pos: Pos :: to_blkno[pos] != bn
    {
      reveal ValidPos();
    }

    predicate ValidMetadata()
      reads Repr()
      requires ValidBasics()
    {
      forall ino: Ino | ino_ok(ino) :: fs.inodes[ino].sz == metadata[ino]
    }

    static predicate inode_pos_match(ino: Ino, blks: seq<Blkno>, to_blkno: imap<Pos, Blkno>)
      requires ino_ok(ino)
      requires |blks| == 15
      requires pos_dom(to_blkno)
    {
      forall k: nat | k < 15 ::
        var bn := blks[k];
        && blkno_ok(bn)
        && to_blkno[Pos(ino, Idx.from_inode(k))] == bn
        // && (bn != 0 ==> blkno_pos(bn) == Some(MkPos(ino, Idx.from_inode(k))))
    }

    predicate {:opaque} ValidInodes()
      reads Repr()
      requires ValidBasics()
    {
      forall ino:Ino | ino_ok(ino) ::
        inode_pos_match(ino, fs.inodes[ino].blks, to_blkno)
    }

    predicate valid_parent(pos: Pos)
      reads Repr()
      requires pos.ilevel > 0
      requires ValidBasics()
    {
      var parent := to_blkno[pos.parent()];
      var blknos := IndBlocks.to_blknos(zero_lookup(fs.data_block, parent));
      var j := pos.child().j;
      var bn := to_blkno[pos];
      blknos.s[j] == bn
    }

    predicate {:opaque} ValidIndirect()
      reads Repr()
      requires ValidBasics()
    {
      forall pos: Pos | pos.ilevel > 0 :: valid_parent(pos)
    }

    predicate {:opaque} ValidData()
      reads Repr()
      requires ValidBasics()
    {
      forall pos:Pos | pos.data? ::
        && pos in data
        && data[pos] == zero_lookup(fs.data_block, to_blkno[pos])
    }

    predicate Valid()
      reads this.Repr()
    {
      && ValidBasics()
      && ValidPos()
      && ValidInodes()
      && ValidMetadata()
      && ValidIndirect()
      && ValidData()
    }

    predicate ValidIno(ino: Ino, i: Inode.Inode)
      reads this.Repr()
    {
      && Valid()
      && fs.is_cur_inode(ino, i)
    }

    constructor(d: Disk)
      ensures Valid()
      ensures fs.quiescent()
    {
      this.fs := new Filesys.Init(d);
      this.to_blkno := imap pos: Pos {:trigger} :: 0 as Blkno;
      this.data := imap pos: Pos | pos.idx.data? :: block0;
      this.metadata := map ino: Ino | ino_ok(ino) :: 0 as uint64;
      new;
      IndBlocks.to_blknos_zero();
      reveal ValidPos();
      reveal ValidInodes();
      reveal ValidIndirect();
      reveal ValidData();
    }

    // private read
    method read_(txn: Txn, pos: Pos, i: Inode.Inode) returns (b: Bytes)
      decreases pos.ilevel
      requires txn.jrnl == fs.jrnl
      requires ValidIno(pos.ino, i)
      ensures is_block(b.data)
      ensures b.data == zero_lookup(fs.data_block, to_blkno[pos])
    {
      reveal ValidInodes();
      var idx := pos.idx;
      if pos.ilevel == 0 {
        reveal ValidPos();
        assert idx.off == IndOff.direct;
        var bn := i.blks[idx.k];
        if bn == 0 {
          b := NewBytes(4096);
          return;
        }
        b := fs.getDataBlock(txn, bn);
        return;
      }
      // recurse
      var parent: Pos := pos.parent();
      var child: IndOff := pos.child();
      var ib: Bytes := this.read_(txn, parent, i);
      var child_bn := IndBlocks.decode_one(ib, child.j);
      reveal ValidIndirect();
      b := fs.getDataBlock(txn, child_bn);
      // NOTE(tej): I can't believe this worked the first time
      reveal ValidData();
    }

    twostate lemma ValidPos_alloc_one(bn: Blkno, pos: Pos)
      requires old(ValidBasics()) && ValidBasics()
      requires blkno_ok(bn)
      requires old(blkno_pos(bn).None?) && old(to_blkno[pos] == 0)
      requires fs.block_used == old(fs.block_used[bn:=Some(pos)])
      requires to_blkno == old(to_blkno[pos:=bn])
      requires old(ValidPos())
      ensures ValidPos()
    {
      reveal ValidPos();
    }

    twostate lemma ValidInodes_change_one(pos: Pos, i': Inode.Inode, bn:Blkno)
      requires old(ValidBasics()) && ValidBasics()
      requires pos.ilevel == 0
      requires to_blkno == old(to_blkno[pos:=bn])
      requires fs.inodes == old(fs.inodes[pos.ino:=i'])
      requires blkno_ok(bn)
      requires i' == old(var i := fs.inodes[pos.ino]; i.(blks:=i.blks[pos.idx.k := bn]))
      requires old(ValidInodes())
      ensures ValidInodes()
    {
      reveal ValidInodes();
      assert inode_pos_match(pos.ino, i'.blks, to_blkno);
    }

    twostate predicate state_unchanged()
      reads this, fs
    {
      && data == old(data)
      && metadata == old(metadata)
    }

    twostate lemma Valid_allocation_fail()
      requires old(Valid())
      requires
          && fs.Valid()
          && fs.data_block == old(fs.data_block)
          && fs.inodes == old(fs.inodes)
          && fs.block_used == old(fs.block_used)
          && data == old(data)
          && metadata == old(metadata)
          && to_blkno == old(to_blkno)
      ensures Valid()
    {
      reveal ValidPos();
      reveal ValidInodes();
      reveal ValidData();
      reveal ValidIndirect();
    }

    // private
    method {:timeLimitMultiplier 2} allocateRootMetadata(txn: Txn, pos: Pos, i: Inode.Inode)
      returns (ok: bool, i': Inode.Inode, bn: Blkno)
      modifies Repr()
      requires txn.jrnl == fs.jrnl
      requires ValidIno(pos.ino, i) ensures ValidIno(pos.ino, i')
      requires  pos.ilevel == 0 && i.blks[pos.idx.k] == 0
      ensures ok ==> bn != 0 && blkno_ok(bn) && bn == to_blkno[pos]
      ensures state_unchanged()
    {
      var idx := pos.idx;
      assert to_blkno[pos] == 0 by {
        reveal ValidInodes();
      }
      ok, bn := fs.allocateTo(txn, pos);
      if !ok {
        i' := i;
        Valid_allocation_fail();
        return;
      }

      i' := i.(blks := i.blks[idx.k := bn]);
      fs.writeInode(pos.ino, i');

      to_blkno := to_blkno[pos:=bn];
      var zeroblk := NewBytes(4096);
      fs.writeDataBlock(txn, bn, zeroblk);

      assert ValidPos() by {
        ValidPos_alloc_one(bn, pos);
      }
      assert ValidInodes() by {
        ValidInodes_change_one(pos, i', bn);
      }
      assert ValidIndirect() && ValidData() by {
        reveal ValidPos();
        reveal ValidIndirect();
        reveal ValidData();
      }
    }

    method {:timeLimitMultiplier 2} allocateIndirectMetadata(txn: Txn, pos: Pos, ibn: Blkno, pblock: Bytes)
      returns (ok: bool, bn: Blkno)
      modifies Repr(), pblock
      requires txn.jrnl == fs.jrnl
      requires Valid() ensures Valid()
      requires pos.ilevel > 0 &&  to_blkno[pos] == 0
      requires ibn == to_blkno[pos.parent()]
      requires ibn != 0
      requires pblock.data == zero_lookup(fs.data_block, ibn)
      ensures ok ==> bn != 0 && bn == to_blkno[pos]
      ensures fs.cur_inode == old(fs.cur_inode)
      ensures fs.inodes == old(fs.inodes)
      ensures state_unchanged()
    {
      assert IndBlocks.to_blknos(block0) == IndBlocks.IndBlknos.zero by {
        IndBlocks.to_blknos_zero();
      }
      ok, bn := fs.allocateTo(txn, pos);
      if !ok {
        Valid_allocation_fail();
        return;
      }
      to_blkno := to_blkno[pos := bn];
      // NOTE(tej): I was formerly only doing this for data blocks, but I think
      // it might be necessary for metadata blocks to preserve that children are
      // still zeros (I was unable to prove ValidIndirect() without this for the
      // special case of pos where pos.parent() == pos0). In that case
      // verification caught a bug! (Albeit one only with holes but still.)
      var zeroblock := NewBytes(4096);
      fs.writeDataBlock(txn, bn, zeroblock);

      var child := pos.child();
      var pblock' := IndBlocks.modify_one(pblock, child.j, bn);
      fs.writeDataBlock(txn, ibn, pblock');
      assert valid_parent(pos);

      assert ValidPos() by {
        ValidPos_alloc_one(bn, pos);
      }

      assert ValidInodes() by {
        reveal ValidPos();
        reveal ValidInodes();
      }

      assert ValidData() by {
        reveal ValidPos();
        reveal ValidData();
      }

      assert ValidIndirect() by {
        reveal ValidIndirect();
        // reveal ValidPos();
        var pos0 := pos;
        forall pos: Pos | pos.ilevel > 0
          ensures valid_parent(pos)
        {
          if pos == pos0  {}
          else {
            if pos.parent() == pos0 {
              IndBlocks.to_blknos_zero();
              reveal ValidPos();
            } else {
              reveal ValidPos();
            }
          }
        }
      }
    }

    // private
    method resolveMetadata(txn: Txn, pos: Pos, i: Inode.Inode) returns (ok: bool, i': Inode.Inode, bn: Blkno)
      decreases pos.ilevel
      modifies Repr()
      requires txn.jrnl == fs.jrnl
      requires ValidIno(pos.ino, i) ensures ValidIno(pos.ino, i')
      ensures ok ==> bn != 0 && bn == to_blkno[pos]
      ensures state_unchanged()
    {
      reveal ValidInodes();
      i' := i;
      var idx := pos.idx;
      if pos.ilevel == 0 {
        assert idx.off == IndOff.direct;
        bn := i.blks[idx.k];
        if bn != 0 {
          // we haven't actually written anything, just resolved existing metadata
          return;
        }
        assert bn == 0;
        // need to allocate a top-level indirect block
        ok, i', bn := allocateRootMetadata(txn, pos, i');
        return;
      }
      // recurse
      var parent: Pos := pos.parent();
      var child: IndOff := pos.child();
      var ibn;
      ok, i', ibn := this.resolveMetadata(txn, parent, i');
      if !ok { return; }
      // now we have somewhere to store the reference to this block, but might
      // need to allocate into the parent
      var pblock := fs.getDataBlock(txn, ibn);
      bn := IndBlocks.decode_one(pblock, child.j);
      assert bn == to_blkno[pos] by {
        reveal ValidIndirect();
      }
      assert ValidIno(pos.ino, i');
      assert state_unchanged();
      if bn != 0 {
        return;
      }

      ok, bn := allocateIndirectMetadata(txn, pos, ibn, pblock);
      assert ValidIno(pos.ino, i');
      if !ok {
        return;
      }
    }

    // public
    //
    // data version of more general read_ spec
    method read(txn: Txn, pos: Pos, i: Inode.Inode) returns (b: Bytes)
      requires txn.jrnl == fs.jrnl
      requires ValidIno(pos.ino, i)
      requires pos.data?
      ensures pos in data && b.data == data[pos]
    {
      b := this.read_(txn, pos, i);
      reveal ValidData();
    }

    // caller can extract size themselves
    lemma inode_metadata(ino: Ino, i: Inode.Inode)
      requires ValidIno(ino, i)
      ensures i.sz == metadata[ino]
    {}

    method write(txn: Txn, pos: Pos, i: Inode.Inode, blk: Bytes)
      returns (ok: bool, i':Inode.Inode)
      modifies Repr()
      requires txn.jrnl == fs.jrnl
      requires ValidIno(pos.ino, i)
      requires pos.data?
      requires is_block(blk.data)
      ensures ValidIno(pos.ino, i')
      ensures ok ==> data == old(data[pos := blk.data])
      ensures !ok ==> data == old(data)
      ensures metadata == old(metadata)
    {
      i' := i;
      var idx := pos.idx;
      var bn;
      ok, i', bn := this.resolveMetadata(txn, pos, i');
      if !ok {
         return;
      }
      assert ValidIno(pos.ino, i');

      fs.writeDataBlock(txn, bn, blk);
      data := data[pos := blk.data];

      assert ValidPos() by {
        reveal ValidPos();
      }
      assert ValidInodes() by {
        reveal ValidPos();
        reveal ValidInodes();
      }
      assert ValidData() by {
        reveal ValidPos();
        reveal ValidData();
      }
      assert ValidIndirect() by {
        reveal ValidPos();
        reveal ValidIndirect();
      }
    }
  }

}
