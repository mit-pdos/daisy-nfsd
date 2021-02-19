include "indirect_fs.dfy"

module BlockFs
{
  import opened Machine
  import opened ByteSlice
  import opened FsKinds
  import opened JrnlTypes
  import opened JrnlSpec
  import opened IndirectPos
  import opened IndFs
  import C = Collections

  datatype preInodeData = InodeData(blks: seq<Block>)
  {
    static const preZero := InodeData(C.repeat(block0, config.total))
    static const zero: InodeData := preZero

    predicate Valid()
    {
      |blks| == config.total
    }
  }
  type InodeData = x:preInodeData | x.Valid() witness preInodeData.preZero

  function inode_data(ino: Ino, data: imap<Pos, Block>): InodeData
    requires ino_ok(ino)
    requires data_dom(data)
  {
    var blks := seq(config.total,
      (n:nat) requires n < config.total => data[Pos.from_flat(ino, n)]);
    InodeData(blks)
  }

  class BlockFilesys
  {
    ghost var data: map<Ino, InodeData>
    const ifs: IndFilesys;


    function metadata(): map<Ino, uint64>
      reads ifs
    {
      ifs.metadata
    }

    function Repr(): set<object>
    {
      {this} + ifs.Repr()
    }

    predicate {:opaque} ValidData()
      reads Repr()
      requires ifs.ValidQ()
    {
      && Fs.ino_dom(data)
      && forall ino: Ino | ino_ok(ino) :: data[ino] == inode_data(ino, ifs.data)
    }

    predicate Valid()
      reads Repr()
    {
      && ifs.ValidQ()
      && ValidData()
    }

    constructor(d: Disk)
      ensures Valid()
      ensures data == map ino: Ino | ino_ok(ino) :: InodeData.zero
    {
      this.ifs := new IndFilesys(d);
      this.data := map ino: Ino | ino_ok(ino) :: InodeData.zero;
      new;
      reveal ValidData();
    }
  }
}
