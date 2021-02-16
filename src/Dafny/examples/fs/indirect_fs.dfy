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
  import C = Collections

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
