include "fs.dfy"

module IndFs
{
  import opened Machine
  import opened ByteSlice
  import opened FsKinds
  import opened JrnlSpec
  import opened Fs
  import opened Marshal
  import C = Collections

  datatype IndBlock = IndBlock(bn: Blkno, blknos: seq<Blkno>, blocks: seq<Block>)
  {
    predicate Valid()
    {
      && blkno_ok(bn)
      && |blknos| == 512
      && |blocks| == 512
      && (forall k: int | 0 <= k < 512 :: blkno_ok(blknos[k]))
    }

    // helps state uniqueness (not just over this IndBlock but all blocks
    // involved in an inode)
    function all_blknos(): seq<Blkno>
    {
      [bn] + blknos
    }

    function zero_lookup(m: map<Blkno, Block>, bn: Blkno): Block
      requires blkno_dom(m)
      requires blkno_ok(bn)
    {
      if bn == 0
        then block0
        else m[bn]
    }

    predicate in_fs(fs: Filesys)
      reads fs.Repr()
      requires fs.Valid()
      requires Valid()
    {
      var b := zero_lookup(fs.data_block, this.bn);
      && block_has_blknos(b, this.blknos)
      && (forall k | 0 <= k < 512 ::
        zero_lookup(fs.data_block, this.blknos[k]) == this.blocks[k])
    }
  }

  predicate block_has_blknos(b: Block, blknos: seq<Blkno>)
  {
    && is_block(b)
    && b == seq_enc_uint64(blknos)
  }

  lemma zero_block_blknos()
    ensures block_has_blknos(block0, C.repeat(0 as Blkno, 512))
  {
    zero_encode_seq_uint64(512);
  }

  lemma block_has_blknos_len(b: Block, blknos: seq<Blkno>)
    requires block_has_blknos(b, blknos)
    ensures |blknos| == 512
  {
    enc_uint64_len(blknos);
    assert 4096 == 512*8;
  }

  method encode_blknos(blknos: seq<Blkno>) returns (bs: Bytes)
    requires |blknos| == 512
    ensures fresh(bs)
    ensures block_has_blknos(bs.data, blknos)
  {
    var enc := new Encoder(4096);
    enc.PutInts(blknos);
    assert enc.enc == C.seq_fmap(encUInt64, blknos);
    enc.is_complete();
    bs := enc.Finish();
    return;
  }

  method decode_blknos(bs: Bytes, ghost blknos: seq<Blkno>) returns (blknos': seq<Blkno>)
    requires block_has_blknos(bs.data, blknos)
    ensures blknos' == blknos
  {
    assert |blknos| == 512 by {
      block_has_blknos_len(bs.data, blknos);
    }
    var dec := new Decoder.Init(bs, C.seq_fmap(encUInt64, blknos));
    assert dec.enc[..512] == dec.enc;
    blknos' := dec.GetInts(512, blknos);
    return;
  }

}
