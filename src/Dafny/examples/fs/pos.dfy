include "kinds.dfy"

// Define Pos, an abstract position for a block in the file system. A Pos is a
// multidimensional index that includes an inode and a location in its metadata
// hierarchy; intermediate locations are metadata while leaves are considered
// data (as described by the data? const in Idx and Pos).
//
// Every type defined here is a subset type that builds-in some Validity
// predicate which restricts all the indices to be in-bounds. To make this work
// we have to declare the structure of an inode as a global constant config:
// Config, which specifies the indirection level for the 15 blocks that are
// stored directly in an inode.

module IndirectPos
{
  import opened FsKinds
  import opened Pow

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
    static function method from_flat(n: nat): (i:Idx)
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

    static lemma from_to_flat_id(n: nat)
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

    static lemma from_flat_inj(n1: nat, n2: nat)
      requires n1 < config.total && n2 < config.total
      ensures from_flat(n1) == from_flat(n2) ==> n1 == n2
    {
      if from_flat(n1) != from_flat(n2) { return; }
      assert from_flat(n1).flat() == from_flat(n2).flat();
      from_to_flat_id(n1);
      from_to_flat_id(n2);
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

    static function method from_flat(ino: Ino, n: nat): Pos
      requires ino_ok(ino)
      requires n < config.total
    {
      Pos(ino, Idx.from_flat(n))
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

}
