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
  import opened Pow
  import C = Collections

  datatype preIndOff = IndOff(ilevel: nat, j: nat)
  {
    static const direct: IndOff := IndOff(0, 0)
    // if this is true then this IndOff points directly to data
    const data?: bool := ilevel == 0

    predicate Valid()
    {
      j < pow(512, ilevel)
    }

    // to dereference an offset, we can decompose it into a single indirection
    // then the remaining lookup at one level lower
    function split(): (p: (IndOff, IndOff))
      requires Valid()
      requires ilevel > 0
    {
      Arith.div_positive_auto();
      var k := pow(512, ilevel-1);
      Arith.div_mod_split(j, k);
      assert pow(512, ilevel) == k * 512;
      Arith.div_incr_auto();
      (IndOff(1, j / k), IndOff(ilevel-1, j % k))
    }

    function parent(): IndOff
      requires Valid()
      requires ilevel > 0
    {
      IndOff(ilevel-1, j / 512)
    }

    function child(): IndOff
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

    function data?(): bool
      requires Valid()
    {
      off.ilevel == config.ilevels[k]
    }

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
      requires this.data?()
    {
      config.totals[k] + off.j
    }

    // from_flat gives us a structured way to find an LBA (we go to its
    // appropriate root block and deference indirect blocks one at a time with
    // i.split() until we get a direct block)
    static function from_flat(n: nat): (i:Idx)
      requires n < config.total
      ensures i.data?()
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

  datatype preRole = Role(ino: Ino, idx: Idx)
  {
    predicate Valid()
    {
      ino_ok(ino)
    }
  }
  type Role = x:preRole | x.Valid() witness Role(0, Idx(0, IndOff(0,0)))
  function MkRole(ino: Ino, idx: Idx): Role
    requires Role(ino, idx).Valid()
  {
    Role(ino, idx)
  }

  predicate role_dom<T>(m: imap<Role, T>)
  {
    forall r:Role :: r in m
  }

  class IndFilesys
  {
    // filesys contains a mapping from allocated Blkno's to roles
    const fs: Filesys<Role>
    // this is a complete map; every position in every inode has a value, but
    // it might be a zero block encoded efficiently via 0's.
    ghost var to_blkno: imap<Role, Blkno>
    // only maps blocks which are used for data (this hides when other blocks
    // change but exposes newly-allocated data blocks)
    ghost var data: map<Blkno, Block>
    ghost var metadata: map<Ino, uint64>

    function blkno_role(bn: Blkno): Option<Role>
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
      && role_dom(to_blkno)
      && ino_dom(metadata)
      // no blkno_dom(data) - domain is a non-trivial subset of blocks
    }

    predicate ValidRoles()
      reads Repr()
      requires ValidBasics()
    {
      && fs.block_used[0].None?
      && (forall bn:Blkno | bn != 0 && blkno_ok(bn) ::
          fs.block_used[bn].Some? ==> to_blkno[fs.block_used[bn].x] == bn)
      && (forall role:Role ::
          var bn := to_blkno[role];
          && blkno_ok(bn)
          && (bn != 0 ==> fs.block_used[bn] == Some(role)))
    }

    lemma blkno_unused(bn: Blkno)
      requires ValidBasics() && ValidRoles()
      requires blkno_ok(bn) && bn != 0 && blkno_role(bn).None?
      ensures forall role: Role :: to_blkno[role] != bn
    {}

    predicate ValidMetadata()
      reads Repr()
      requires ValidBasics()
    {
      forall ino: Ino | ino_ok(ino) :: fs.inodes[ino].sz == metadata[ino]
    }

    predicate ValidInodes()
      reads Repr()
      requires ValidBasics()
    {
      forall ino:Ino | ino_ok(ino) ::
        forall k | 0 <= k < 15 ::
        var bn := fs.inodes[ino].blks[k];
        && blkno_ok(bn)
        && to_blkno[Role(ino, Idx.from_inode(k))] == bn
        && (bn != 0 ==> fs.block_used[bn] == Some(MkRole(ino, Idx.from_inode(k))))
    }

    predicate ValidIndirect()
      reads Repr()
      requires ValidBasics()
    {
      // TODO: say something about every ilevel > 0 being located in its parent
      true
    }

    predicate ValidData()
      reads Repr()
      requires ValidBasics()
    {
      forall bn:Blkno | bn != 0  && blkno_ok(bn) ::
        blkno_role(bn).Some? && blkno_role(bn).x.idx.data?() ==>
        && bn in data
        && data[bn] == fs.data_block[bn]
    }

    predicate Valid()
      reads this.Repr()
    {
      && ValidBasics()
      && ValidRoles()
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
      this.to_blkno := imap role: Role | role.Valid() :: 0;
      // no allocated data blocks initially
      this.data := map[];
      this.metadata := map ino: Ino | ino_ok(ino) :: 0 as uint64;
    }

    method write(txn: Txn, ghost ino: Ino, i: Inode.Inode, idx: Idx, blk: Bytes) returns (ok: bool, i':Inode.Inode)
      modifies Repr()
      requires txn.jrnl == fs.jrnl
      requires ValidIno(ino, i)
      requires idx.data?()
      requires is_block(blk.data)
      ensures ValidIno(ino, i')
    {
      i' := i;
      if idx.ilevel == 0 {
        assert idx.off == IndOff.direct;
        // this index is found directly in the inode
        var bn := i.blks[idx.k];
        if bn == 0 {
          ok, bn := fs.allocateTo(txn, Role(ino, idx));
          if !ok {
            return;
          }
          i' := i.(blks := i.blks[idx.k:=bn]);
          fs.writeInode(ino, i');
          to_blkno := to_blkno[Role(ino, idx):=bn];
          fs.writeDataBlock(txn, bn, blk);
          data := data[bn := blk.data];
          return;
        }
        fs.writeDataBlock(txn, bn, blk);
        data := data[bn := blk.data];
        return;
      }
      // TODO
      i' := i;
      assume false;
    }
  }

}
