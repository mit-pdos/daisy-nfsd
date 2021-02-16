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
      // TODO: how to brute force this?
      assume false;
    }
    assert config.totals[0] == totals[0];
    assert config.ilevels[..1] == config.ilevels[..1];
    calc {
      config.totals[1];
      Config.configTotal(config.ilevels[..1]);
      1;
    }
  }

  datatype preIdx = Idx(k: nat, off: IndOff)
  {
    function data?(): bool
      requires Valid()
    {
      off.ilevel == config.ilevels[k]
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

  class IndFilesys
  {
    const fs: Filesys<()>

    function Repr(): set<object>
    {
      {this} + fs.Repr()
    }

    predicate Valid()
      reads this.Repr()
    {
      && fs.Valid()
    }

    constructor(d: Disk)
      ensures Valid()
    {
      this.fs := new Filesys.Init(d);
    }
  }

}
