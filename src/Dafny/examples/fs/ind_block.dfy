include "../../machine/machine.s.dfy"
include "../../jrnl/jrnl.s.dfy"
include "../../util/marshal.i.dfy"

module IndBlocks
{
  import opened Machine
  import opened JrnlTypes
  import opened JrnlSpec

  import opened ByteSlice
  import opened Marshal

  datatype preIndBlknos = IndBlknos(s: seq<Blkno>)
  {
    static const preZero := IndBlknos(C.repeat(0 as Blkno, 512))
    static const zero: IndBlknos := preZero

    predicate Valid()
    {
      |s| == 512
    }
  }
  type IndBlknos = x:preIndBlknos | x.Valid() witness preIndBlknos.preZero

  predicate block_has_blknos(b: Block, blknos: IndBlknos)
  {
    && b == seq_enc_uint64(blknos.s)
  }

  lemma zero_block_blknos()
    ensures block_has_blknos(block0, IndBlknos.zero)
  {
    zero_encode_seq_uint64(512);
  }

  method encode_blknos(blknos: IndBlknos) returns (bs: Bytes)
    ensures fresh(bs)
    ensures is_block(bs.data) && block_has_blknos(bs.data, blknos)
  {
    var enc := new Encoder(4096);
    enc.PutInts(blknos.s);
    assert enc.enc == C.seq_fmap(encUInt64, blknos.s);
    enc.is_complete();
    bs := enc.Finish();
    return;
  }

  method decode_blknos(bs: Bytes, ghost blknos: IndBlknos) returns (blknos': seq<Blkno>)
    requires is_block(bs.data) && block_has_blknos(bs.data, blknos)
    ensures blknos' == blknos.s
  {
    var dec := new Decoder.Init(bs, C.seq_fmap(encUInt64, blknos.s));
    assert dec.enc[..512] == dec.enc;
    blknos' := dec.GetInts(512, blknos.s);
    return;
  }

  function to_blknos(bs: Block): (blknos:IndBlknos)
    ensures block_has_blknos(bs, blknos)
  {
    IndBlknos(decode_uint64_seq(bs))
  }

  lemma to_blknos_zero()
    ensures to_blknos(block0) == IndBlknos.zero
  {
    // TODO: figure out the best way to prove this
    assume false;
  }

}
