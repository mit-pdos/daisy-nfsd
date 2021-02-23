include "../../machine/machine.s.dfy"
include "../../util/marshal.i.dfy"
include "kinds.dfy"

module DirEntries
{
  import opened Machine
  import opened ByteSlice
  import opened FsKinds
  import opened Marshal
  import C = Collections

  // TODO: how should we represent paths for the user? the types here are
  // convenient value types for verification but horrendous in Go; we could use
  // Bytes and then check that they satisfy all these constraints. That would be
  // fairly realistic.

  type String = seq<byte>

  predicate is_pathc(s: String)
  {
    && |s| <= 24
    && forall i | 0 <= i < |s| :: s[i] != 0
  }

  type PathComp = s:String | is_pathc(s)

  function method encode_pathc(pc: PathComp): (s:seq<byte>)
    ensures |s| == 24
  {
    pc + C.repeat(0 as byte, 24 - |pc|)
  }

  function method decode_null_terminated(s: seq<byte>): String
  {
    if s == [] then []
    else
      if s[0] == 0 then []
      else [s[0]] + decode_null_terminated(s[1..])
  }

  // decode_null_terminated is technically the longest sequence satisfying these properties
  lemma decode_null_terminated_spec(s: seq<byte>)
    ensures C.prefix_of(decode_null_terminated(s), s)
    ensures forall i | 0 <= i < |decode_null_terminated(s)| :: decode_null_terminated(s)[i] != 0
  {}

  function method decode_pathc(s: seq<byte>): PathComp
    requires |s| == 24
  {
    decode_null_terminated_spec(s);
    decode_null_terminated(s)
  }

  lemma {:induction s1} decode_nullterm_prefix(s1: seq<byte>, s2: seq<byte>)
    requires forall i | 0 <= i < |s1| :: s1[i] != 0
    ensures decode_null_terminated(s1 + s2) == s1 + decode_null_terminated(s2)
  {
    if s1 == [] {
      assert s1 + s2 == s2;
    } else {
      assert (s1 + s2)[1..] == s1[1..] + s2;
    }
  }

  lemma decode_all_null(count: nat)
    ensures decode_null_terminated(C.repeat(0 as byte, count)) == []
  {}

  lemma decode_encode(pc: PathComp)
    ensures decode_pathc(encode_pathc(pc)) == pc
  {
    decode_nullterm_prefix(pc, C.repeat(0 as byte, 24 - |pc|));
    decode_all_null(24 - |pc|);
  }

  datatype DirEnt = DirEnt(name: PathComp, ino: Ino)
  {
    function {:opaque} encoding(): seq<Encodable>
    {
      [EncBytes(encode_pathc(name)), EncUInt64(ino)]
    }

    function enc(): seq<byte>
    {
      Marshal.seq_encode(encoding())
    }

    lemma enc_app()
      ensures enc() == encode_pathc(name) + IntEncoding.le_enc64(ino)
    {
      reveal encoding();
      //assert enc() == seq_encode([EncBytes(encode_pathc(name)), EncUInt64(ino)]);
      seq_encode_unfold([EncBytes(encode_pathc(name)), EncUInt64(ino)]);
    }

    lemma enc_len()
      ensures |enc()| == 32
    {
      enc_app();
    }

    method encode() returns (bs:Bytes)
      ensures fresh(bs) && bs.Valid() && bs.data == enc()
    {
      var enc := new Encoder(32);
      enc.PutByteSeq(encode_pathc(name));
      enc.PutInt(ino);
      bs := enc.Finish();
      reveal encoding();
    }

    static method decode(bs: Bytes, ghost ent: DirEnt) returns (ent': DirEnt)
      requires bs.data == ent.enc()
      ensures ent' == ent
    {
      assert |bs.data| == 32 by { ent.enc_len(); }
      var dec := new Decoder.Init(bs, ent.encoding());
      reveal ent.encoding();
      var name_s := dec.GetByteSeq(24, encode_pathc(ent.name));
      var ino := dec.GetInt(ent.ino);
      ent' := DirEnt(decode_pathc(name_s), ino);
      decode_encode(ent.name);
    }
  }
}
