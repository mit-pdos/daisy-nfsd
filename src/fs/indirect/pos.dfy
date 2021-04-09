include "../super.dfy"

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
  import opened Machine
  import C = Collections

  datatype preIndOff = IndOff(ilevel: uint64, j: uint64)
  {
    static const direct: IndOff := IndOff(0, 0)

    predicate Valid()
    {
      j as nat < pow(512, ilevel as nat)
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

  function method pow64(x: uint64, k: uint64): (p:uint64)
    requires 0 < x
    requires pow(x as nat, k as nat) < U64.MAX
    ensures p as nat == pow(x as nat, k as nat)
  {
    if k == 0 then 1 else (
      Pow.pow_incr(x as nat, (k-1) as nat, k as nat);
      x * pow64(x, k-1)
    )
  }

  datatype Config = Config(ilevels: seq<uint64>)
  {
    const total := sum_nat(ilevels)

    predicate Valid()
    {
      total < U64.MAX
    }

    function method total_to(k: uint64): (t:uint64)
      requires Valid()
      requires k as nat <= |ilevels|
      ensures t as nat == sum_nat(ilevels[..k])
      ensures t as nat <= total
    {
      sum_nat_prefix_lt(ilevels, k as nat);
      sum(ilevels[..k])
    }

    function method totals(): seq<uint64>
      requires Valid()
    {
      sums(ilevels)
    }

    function method total_u64(): (t:uint64)
      requires Valid()
      ensures t as nat == total
    {
      sum(ilevels)
    }

    static function method sum_nat(ilevels: seq<uint64>): nat
    {
      if ilevels == [] then 0
      else pow(512, ilevels[0] as nat) + sum_nat(ilevels[1..])
    }

    static function method sum(ilevels: seq<uint64>): (s:uint64)
      requires sum_nat(ilevels) < U64.MAX
      ensures s as nat == sum_nat(ilevels)
    {
      if ilevels == [] then 0
      else pow64(512, ilevels[0]) + sum(ilevels[1..])
    }

    static lemma test_configSum1()
      ensures sums([0]) == [0,1]
    {}

    static lemma test_configSum2()
      ensures sums([0,1]) == [0,1,1+512]
    {
      forall i | 0 <= i < 3
        ensures sums([0,1])[i] == [0,1,1+512][i]
      {
        assert [0,1][..0] == [];
        assert [0,1][..1] == [0];
        assert [0,1][..2] == [0,1];
      }
    }

    static lemma {:induction n} sum_repeat0(n: nat)
      ensures sum_nat(C.repeat(0 as uint64, n)) == n
    {
      if n > 0 {
        C.repeat_unfold(0 as uint64, n);
        sum_repeat0(n-1);
      }
    }

    static lemma {:induction ilevels1} sum_app(ilevels1: seq<uint64>, ilevels2: seq<uint64>)
      ensures sum_nat(ilevels1 + ilevels2) == sum_nat(ilevels1) + sum_nat(ilevels2)
    {
      if |ilevels1| == 0 {
        assert ilevels1 + ilevels2 == ilevels2;
      } else {
        assert (ilevels1 + ilevels2)[1..] == ilevels1[1..] + ilevels2;
        sum_app(ilevels1[1..], ilevels2);
      }
    }

    static lemma sum_nat_prefix_lt(ilevels: seq<uint64>, k: nat)
      requires k <= |ilevels|
      ensures sum_nat(ilevels[..k]) <= sum_nat(ilevels)
    {
      sum_app(ilevels[..k], ilevels[k..]);
      assert ilevels == ilevels[..k] + ilevels[k..];
    }

    static function method sums(ilevels: seq<uint64>): (s:seq<uint64>)
      requires sum_nat(ilevels) < U64.MAX
    {
      seq(1+|ilevels|, (i:nat) requires i <= |ilevels| =>
        (sum_nat_prefix_lt(ilevels, i);
        sum(ilevels[..i]))
          )
    }

  }

  const config: Config := Config([0,0,0,0,0,0,0,0,0,0,1,1,1,3])

  lemma config_properties()
    ensures config.Valid()
    ensures |config.ilevels| == 14
    ensures config.total == 10 + 3*512 + 512*512*512
    // these inodes can hold at least 10GB
    ensures config.total * 4 / 1024 /* MB */ > 10_000
  {}

  lemma config_total_to(k: uint64)
    requires k as nat < |config.ilevels|
    ensures config.total_to(k) == config.totals()[k]
  {}

  lemma config_totals_after_10(k: nat)
    requires 10 <= k < |config.ilevels|
    ensures Config.sum_nat([1,1,1,3][..k-10]) <= 10+3*512+512*512*512
    ensures config.totals()[k] == 10 + Config.sum([1,1,1,3][..k-10])
  {
    // config.totals()[k] == Config.sum_nat(config.ilevels[..k])
    assert config.ilevels[..k] == config.ilevels[..10] + config.ilevels[10..][..k-10];
    Config.sum_app(config.ilevels[..10], config.ilevels[10..][..k-10]);
    assert config.ilevels[..10] == [0,0,0,0,0,0,0,0,0,0];
    assert Config.sum_nat([0,0,0,0,0,0,0,0,0,0]) == 10;
    assert Config.sum_nat(config.ilevels[..10]) == 10;
    Config.sum_nat_prefix_lt([1,1,1,3], k-10);
  }

  lemma config_totals()
    ensures config.totals() == [0,1,2,3,4,5,6,7,8,9,10,10+512,10+2*512,10+3*512, 10+3*512 + 512*512*512]
  {
    var totals: seq<uint64> := [0,1,2,3,4,5,6,7,8,9,10,10+512,10+2*512,10+3*512, 10+3*512 + 512*512*512];
    assert [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 3][..0] == [];
    assert [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 3][..1] == [0];
    assert [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 3][..2] == [0, 0];
    assert [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 3][..3] == [0, 0, 0];
    assert [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 3][..4] == [0, 0, 0, 0];
    assert [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 3][..5] == [0, 0, 0, 0, 0];
    assert [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 3][..6] == [0, 0, 0, 0, 0, 0];
    assert [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 3][..7] == [0, 0, 0, 0, 0, 0, 0];
    assert [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 3][..8] == [0, 0, 0, 0, 0, 0, 0, 0];
    assert [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 3][..9] == [0, 0, 0, 0, 0, 0, 0, 0, 0];
    assert [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 3][..10] == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    //assert [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 3][..11] == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
    //assert [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 3][..12] == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1];
    //assert [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 3][..13] == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1];
    assert [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 3][..14] == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 3];
    assert config.totals()[0] == totals[0];
    assert config.totals()[1] == totals[1];
    assert config.totals()[2] == totals[2];
    assert config.totals()[3] == totals[3];
    assert config.totals()[4] == totals[4];
    assert config.totals()[5] == totals[5];
    assert config.totals()[6] == totals[6];
    assert config.totals()[7] == totals[7];
    assert config.totals()[8] == totals[8];
    assert config.totals()[9] == totals[9];
    assert config.totals()[10] == totals[10];
    assert config.totals()[11] == totals[11] by {
      config_totals_after_10(11);
    }
    assert config.totals()[12] == totals[12] by {
      assert [1,1,1,3][..2] == [1,1];
      config_totals_after_10(12);
    }
    assert config.totals()[13] == totals[13] by {
      assert [1,1,1,3][..3] == [1,1,1];
      config_totals_after_10(13);
    }
    assert config.totals()[14] == totals[14];
  }

  datatype preIdx = Idx(k: uint64, off: IndOff)
  {
    const ilevel: uint64 := off.ilevel
    predicate method data?()
    {
      && k as nat < |config.ilevels|
      && off.ilevel == config.ilevels[k]
    }


    static function from_inode(k: uint64): Idx
      requires k as nat < |config.ilevels|
    {
      Idx(k, IndOff.direct)
    }

    predicate Valid()
    {
      && k as nat < |config.ilevels|
      && off.ilevel <= config.ilevels[k]
    }

    // "flat" indices are logical block addresses (LBAs) for the inode
    function flat(): uint64
      requires Valid()
      requires this.data?()
    {
      config.total_to(k) + off.j
    }

    // from_flat gives us a structured way to find an LBA (we go to its
    // appropriate root block and deference indirect blocks one at a time with
    // i.split() until we get a direct block)
    static function method from_flat(n: uint64): (i:Idx)
      requires n < config.total as uint64
      ensures i.data?()
    {
      if n < 10 then
        Idx(n, IndOff.direct)
      else (
        var n: uint64 := n-10;
        if n < 3*512 then
          Idx(10+n/512, IndOff(1, n%512))
        else (
          var n: uint64 := n-3*512;
          // there's only one triply-indirect block so no complicated
          // calculations are needed here
          Idx(13, IndOff(3, n))
        )
      )
    }

    static lemma from_to_flat_id(n: uint64)
      requires n as nat < config.total
      ensures from_flat(n).flat() == n
    {
      config_totals();
      if n < 10 {
        assert from_flat(n) == Idx(n, IndOff.direct);
        return;
      }
      assert n >= 10;
      var n0: uint64 := n;
      var n: uint64 := n-10;
      if n < 3*512 {
        assert 10 <= from_flat(n0).k < 13;
        if n < 512 {
          assert from_flat(n0).k == 10;
          return;
        }
        if n < 2*512 {
          assert from_flat(n0).k == 11;
          assert config.total_to(11) == 10+512 by {
            config_totals_after_10(11);
          }
          return;
        }
        assert from_flat(n0).k == 12;
        assert config.total_to(12) == 10+2*512 by {
          config_totals_after_10(12);
        }
        return;
      }
      assert from_flat(n0).k == 13;
      assert config.total_to(13) == 10+3*512 by {
        config_totals();
        config_total_to(13);
      }
      assert from_flat(n0).flat() == 10+3*512 + (n-3*512);
  }

    static lemma from_flat_inj(n1: uint64, n2: uint64)
      requires n1 as nat < config.total && n2 as nat < config.total
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
    const ilevel: uint64 := idx.off.ilevel;
    const data?: bool := idx.data?()

    static function method from_flat(ino: Ino, n: uint64): Pos
      requires n as nat < config.total
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
