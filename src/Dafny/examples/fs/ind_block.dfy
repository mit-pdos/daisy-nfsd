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
    assert seq_encode(C.seq_fmap(encUInt64, C.repeat(0 as uint64, 512))) == block0 by {
      var es := C.repeat(EncUInt64(0), 512);
      assert C.seq_fmap(encUInt64, C.repeat(0 as uint64, 512)) == es;
      assert seq_encode(es) == C.concat(C.repeat(enc_encode(EncUInt64(0)), 512)) by {
        seq_encode_concat(es);
        assert C.seq_fmap(enc_encode, es) == C.repeat(enc_encode(EncUInt64(0)), 512);
      }
      assert enc_encode(EncUInt64(0)) == C.repeat(0 as byte, 8) by {
        IntEncoding.lemma_enc_0();
      }
      C.concat_repeat(0 as byte, 8, 512);
    }
    assert decode_uint64_seq(block0) == C.repeat(0 as uint64, 512) by {
      decode_encode_uint64_seq_id(C.repeat(0 as uint64, 512));
    }
  }

  method decode_one(bs: Bytes, k: nat) returns (bn:Blkno)
    requires is_block(bs.data)
    requires k < 512
    ensures bn == to_blknos(bs.data).s[k]
  {
    bn := IntEncoding.UInt64Get(bs, (k as uint64)*8);
    assert bn == decode_uint64_seq_one(bs.data, k);
    decode_uint64_seq_one_spec(bs.data, k);
  }

  // this could be done in-place on bs more efficiently (and the spec allows it
  // to return bs)
  method modify_one(bs: Bytes, k: nat, bn: Blkno) returns (bs': Bytes)
    modifies bs
    requires is_block(bs.data)
    requires k < 512
    ensures is_block(bs'.data)
    ensures (
    var blknos' := to_blknos(bs'.data);
    var blknos := old(to_blknos(bs.data));
    blknos' == blknos.(s:=blknos.s[k := bn]))
  {
    var blknos := decode_blknos(bs, to_blknos(bs.data));
    blknos := blknos[k := bn];
    bs' := encode_blknos(IndBlknos(blknos));
    decode_encode_uint64_seq_id(blknos);
  }

}
