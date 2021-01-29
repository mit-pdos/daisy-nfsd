include "fs.dfy"

module ByteFs {
  import opened Fs
  import opened Machine

  // TODO: implement this on top of the lower-level API in fs.dfy

  function inode_data(sz: nat, blks: seq<Block>): (bs:seq<byte>)
    requires forall i:nat | i < |blks| :: is_block(blks[i])
    requires |blks| == Round.div_roundup_alt(sz, 4096)
    ensures |bs| == sz
  {
    if sz % 4096 == 0 then (
      C.concat_homogeneous_spec(blks, 4096);
      C.concat(blks)
      )
    else (
      C.concat_homogeneous_spec(C.without_last(blks), 4096);
      C.concat(C.without_last(blks)) +
      C.last(blks)[..sz % 4096]
      )
  }
}
