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

  type IndBlknos = bns:seq<Blkno> | |bns| == 512 witness C.repeat(0 as Blkno, 512)
  const indBlknos0: IndBlknos := C.repeat(0 as Blkno, 512)

  predicate block_has_blknos(b: Block, blknos: IndBlknos)
  {
    && b == seq_enc_uint64(blknos)
  }

  lemma zero_block_blknos()
    ensures block_has_blknos(block0, indBlknos0)
  {
    zero_encode_seq_uint64(512);
  }

  method encode_blknos(blknos: IndBlknos) returns (bs: Bytes)
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

  method decode_blknos(bs: Bytes, ghost blknos: IndBlknos) returns (blknos': seq<Blkno>)
    requires is_block(bs.data) && block_has_blknos(bs.data, blknos)
    ensures blknos' == blknos
  {
    var dec := new Decoder.Init(bs, C.seq_fmap(encUInt64, blknos));
    assert dec.enc[..512] == dec.enc;
    blknos' := dec.GetInts(512, blknos);
    return;
  }

}
