include "../../machine/machine.s.dfy"
include "../../jrnl/jrnl.s.dfy"
include "../../util/marshal.i.dfy"

module IndBlocks
{
  import opened Machine
  import opened JrnlSpec

  import opened ByteSlice
  import opened Marshal

  predicate block_has_blknos(b: Block, blknos: seq<Blkno>)
  {
    && b == seq_enc_uint64(blknos)
    && |blknos| == 512
  }

  // there are two redundant length expressions in block_has_blknos, we can use
  // either of them to prove block_has_blknos
  lemma block_has_blknos_len(b: Block, blknos: seq<Blkno>)
    requires b == seq_enc_uint64(blknos)
    ensures block_has_blknos(b, blknos)
  {
    enc_uint64_len(blknos);
    assert 4096 == 512*8;
  }

  lemma zero_block_blknos()
    ensures block_has_blknos(block0, C.repeat(0 as Blkno, 512))
  {
    zero_encode_seq_uint64(512);
  }

  method encode_blknos(blknos: seq<Blkno>) returns (bs: Bytes)
    requires |blknos| == 512
    ensures fresh(bs)
    ensures is_block(bs.data) && block_has_blknos(bs.data, blknos)
  {
    var enc := new Encoder(4096);
    enc.PutInts(blknos);
    assert enc.enc == C.seq_fmap(encUInt64, blknos);
    enc.is_complete();
    bs := enc.Finish();
    return;
  }

  method decode_blknos(bs: Bytes, ghost blknos: seq<Blkno>) returns (blknos': seq<Blkno>)
    requires is_block(bs.data) && block_has_blknos(bs.data, blknos)
    ensures blknos' == blknos
  {
    var dec := new Decoder.Init(bs, C.seq_fmap(encUInt64, blknos));
    assert dec.enc[..512] == dec.enc;
    blknos' := dec.GetInts(512, blknos);
    return;
  }

}
