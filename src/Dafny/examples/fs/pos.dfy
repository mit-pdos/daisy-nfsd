include "kinds.dfy"

// Define Pos, an abstract position for a block in the file system. A Pos is a
// multidimensional index that includes an inode and a location in its metadata
// hierarchy; intermediate locations are metadata while leaves are considered
// data (as described by the data? const in Idx and Pos).
//
// Every type defined here is a subset type that builds-in some Validity
// predicate which restricts all the indices to be in-bounds. To make this work
// we have to declare the structure of an inode as a global constant config:
// Config, which specifies the indirection level for the 14 blocks that are
// stored directly in an inode.

module IndirectPos
{
  import opened FsKinds
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
    const totals := sums(ilevels)
    const total := sum(ilevels)

    static function method sum(ilevels: seq<nat>): nat
    {
      if ilevels == [] then 0
      else pow(512, ilevels[0]) + sum(ilevels[1..])
    }

    static lemma test_configSum1()
      ensures sums([0]) == [0,1]
    {}

    static lemma test_configSum2()
      ensures sums([0,1]) == [0,1,1+512]
    {
      assert [0,1][..1] == [0];
    }

    static lemma test_configSum3()
      ensures sums([0,0,1,2]) == [0,1,2,2+512, 2+512+512*512]
    {
      assert sum([0,0,1,2]) == 2+512+512*512;
      assert [0,0,1,2][..3] == [0,0,1];
      assert [0,0,1][..2] == [0,0];
      assert [0,0][..1] == [0];
    }

    static lemma {:induction n} sum_repeat0(n: nat)
      ensures sum(C.repeat(0 as nat, n)) == n
    {
      if n > 0 {
        C.repeat_unfold(0 as nat, n);
        sum_repeat0(n-1);
      }
    }

    static lemma {:induction ilevels1} sum_app(ilevels1: seq<nat>, ilevels2: seq<nat>)
      ensures sum(ilevels1 + ilevels2) == sum(ilevels1) + sum(ilevels2)
    {
      if |ilevels1| == 0 {
        assert ilevels1 + ilevels2 == ilevels2;
      } else {
        assert (ilevels1 + ilevels2)[1..] == ilevels1[1..] + ilevels2;
        sum_app(ilevels1[1..], ilevels2);
      }
    }

    static function method sums(ilevels: seq<nat>): (s:seq<nat>)
      ensures |s| == 1+|ilevels|
      ensures forall i | 0 <= i <= |ilevels| :: s[i] == sum(ilevels[..i])
    {
      if ilevels == [] then [0]
      else (
        assert ilevels[..|ilevels|] == ilevels;
        var s := sums(ilevels[..|ilevels|-1]) + [sum(ilevels)];
        assert s[|ilevels|] == sum(ilevels);
        // NOTE(tej): need to assert this to get into statement context; see
        // https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#2036-statements-in-an-expression
        // which does not include forall statements
        assert forall i | 0 <= i <= |ilevels| :: s[i] == sum(ilevels[..i]) by
        {
          forall i | 0 <= i <= |ilevels|
            ensures s[i] == sum(ilevels[..i])
          {
            if i == |ilevels| {}
            else {
              calc {
                s[i];
                sums(ilevels[..|ilevels|-1])[i];
                { assert ilevels[..|ilevels|-1][..i] == ilevels[..i]; }
                sum(ilevels[..i]);
              }
            }
          }
        }
        s
      )
    }

  }

  const config: Config := Config([0,0,0,0,0,0,0,0,0,0,1,1,1,3])

  lemma config_properties()
    ensures |config.ilevels| == 14
    ensures config.total == 10 + 3*512 + 512*512*512
    // these inodes can hold at least 10GB
    ensures config.total * 3 / 1024 /* MB */ > 10_000
  {}

  lemma config_totals()
    ensures config.totals == [0,1,2,3,4,5,6,7,8,9,10,10+512,10+2*512,10+3*512, 10+3*512 + 512*512*512]
  {
    var totals := [0,1,2,3,4,5,6,7,8,9,10,10+512,10+2*512,10+3*512, 10+3*512 + 512*512*512];
    forall i | 0 <= i <= 14
      ensures config.totals[i] == Config.sum(config.ilevels[..i])
    {
    }
    // TODO: this somehow helps? this proof is probably unstable
    assert config.ilevels[10..12] == [1,1];
    forall i | 0 <= i <= 14
      ensures Config.sum(config.ilevels[..i]) == totals[i]
    {
      if i <= 10 {
        assert config.ilevels[..i] == C.repeat(0 as nat, i);
        Config.sum_repeat0(i);
      } else {
        assert config.ilevels[..i] == C.repeat(0 as nat, 10) + config.ilevels[10..i];
        Config.sum_repeat0(10);
        Config.sum_app(C.repeat(0 as nat, 10), config.ilevels[10..i]);
        assert config.ilevels[10..12] == [1,1];
        assert config.sum(config.ilevels[10..12]) == Config.sum([1,1]) == 2*512;
        assert config.ilevels[10..13] == [1,1,1];
        assert config.sum(config.ilevels[10..13]) == Config.sum([1,1,1]) == 3*512;
        assert config.ilevels[10..14] == [1,1,1,3];
        assert config.sum(config.ilevels[10..14]) == Config.sum([1,1,1,3]) == 3*512 + 512*512*512;
      }
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
        if n < 3*512 then
          Idx(10+n/512, IndOff(1, n%512))
        else (
          var n: nat := n-3*512;
          // there's only one triply-indirect block so no complicated
          // calculations are needed here
          Idx(13, IndOff(3, n))
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
      if n < 3*512 {
        assert 10 <= from_flat(n0).k < 13;
        if n < 512 {
          return;
        }
        if n < 2*512 {
          return;
        }
        return;
      }
      assert from_flat(n0).flat() == 10+3*512 + (n-3*512);
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
  datatype Pos = Pos(ino: Ino, idx: Idx)
  {
    const ilevel: nat := idx.off.ilevel;
    const data?: bool := idx.data?

    static function method from_flat(ino: Ino, n: nat): Pos
      requires n < config.total
    {
      Pos(ino, Idx.from_flat(n))
    }

    function method parent(): Pos
      requires ilevel > 0
    {
      Pos(ino, Idx(idx.k, idx.off.parent()))
    }

    function method child(): IndOff
      requires ilevel > 0
    {
      idx.off.child()
    }

  }

}
