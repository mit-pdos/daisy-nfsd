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
    static const zero := DirEnt([], 0 as Ino)

    // we don't call this valid because unused DirEnts do show up (eg, a Dirents
    // will in general have unused DirEnts and this isn't a problem)
    predicate method used()
    {
      ino != 0
    }

    predicate method unused()
    {
      ino == 0
    }

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

  type Directory = map<PathComp, Ino>

  function seq_to_dir(s: seq<DirEnt>): Directory
  {
    if s == [] then map[]
    else (
      var e := s[0];
      var s' := s[1..];
      if e.used() then
        seq_to_dir(s')[e.name := e.ino]
      else seq_to_dir(s')
      )
  }

  lemma test_seq_to_dir_overwrite()
  {
    var e1 := DirEnt([1], 1 as Ino);
    var e2 := DirEnt([1], 2 as Ino);
    var e3 := DirEnt([2], 0 as Ino);
    // the first entry should take precedence
    assert seq_to_dir([e1, e2, e3])[e1.name] == 1 as Ino;
    assert seq_to_dir([e3]) == map[];
    assert seq_to_dir([e2, e3]) == seq_to_dir([e2]);
    assert seq_to_dir([e1, e2, e3]) == seq_to_dir([e1, e2]);
  }

  lemma {:induction count} seq_to_dir_zeros(count: nat)
    ensures seq_to_dir(C.repeat(DirEnt.zero, count)) == map[]
  {
    if count > 0 {
      C.repeat_unfold(DirEnt.zero, count);
    }
  }

  lemma {:induction s, i} seq_to_dir_insert(s: seq<DirEnt>, i: nat, e: DirEnt)
    requires i < |s|
    requires forall k: nat | k < i :: s[k].name != e.name || !s[k].used()
    requires e.used()
    requires !s[i].used()
    ensures seq_to_dir(s[i := e]) == seq_to_dir(s)[e.name := e.ino]
  {
    // if s == [] { assert false; }
    // if i == 0 {
    //   assert seq_to_dir(s[i := e]) == seq_to_dir(s[1..])[e.name := e.ino];
    // } else {
    //   seq_to_dir_insert(s[1..], i-1, e);
    // }
  }

  datatype preDirents = Dirents(s: seq<DirEnt>)
  {
    static const zero: Dirents := Dirents(C.repeat(DirEnt.zero, 128))

    ghost const dir: Directory := seq_to_dir(s)

    static lemma zero_dir()
      ensures zero.dir == map[]
    {
      seq_to_dir_zeros(128);
    }

    predicate Valid()
    {
      // 128*32 == 4096 so these will fit in a block
      |s| == 128
    }

    static function encOne(e: DirEnt): seq<byte>
    {
      e.enc()
    }

    function enc(): seq<byte>
    {
      C.concat(C.seq_fmap(encOne, this.s))
    }

    lemma enc_len()
      requires Valid()
      ensures |enc()| == 4096
    {
      forall e: DirEnt
        ensures |encOne(e)| == 32
      {
        e.enc_len();
      }
      C.concat_homogeneous_len(C.seq_fmap(encOne, this.s), 32);
    }

    method encode() returns (bs:Bytes)
      requires Valid()
      ensures fresh(bs) && bs.Valid() && bs.data == enc()
    {
      // TODO: implement
      assume false;
    }

    static method decode(b: Bytes, ghost ents: Dirents) returns (ents': Dirents)
      requires b.data == ents.enc()
      ensures ents' == ents
    {
      // TODO: implement
      assume false;
    }

    function method insert_ent(i: nat, e: DirEnt): (ents': Dirents)
      requires Valid()
      requires i < 128
      ensures ents'.Valid()
    {
      var s' := this.s[i := e];
      var ents': preDirents := Dirents(s');
      assert ents'.Valid();
      ents'
    }

    lemma insert_ent_dir(e: DirEnt)
      requires Valid()
      requires this.findName(e.name) >= 128
      requires this.findFree() < 128 && e.used()
      ensures this.insert_ent(this.findFree(), e).dir == this.dir[e.name := e.ino]
    {
      reveal find_name_spec();
      seq_to_dir_insert(s, this.findFree(), e);
    }

    predicate {:opaque} find_name_spec(p: PathComp, i: nat)
    {
      && i <= |s|
      && forall k:nat | k < i :: !(s[k].used() && s[k].name == p)
    }

    function method findName(p: PathComp): (i:nat)
      requires Valid()
      ensures i < 128 ==> s[i].used() && s[i].name == p
      ensures find_name_spec(p, i)
    {
      var f := (e:DirEnt) => e.used() && e.name == p;
      C.find_first_complete(f, s);
      reveal find_name_spec();
      C.find_first(f, s)
    }

    predicate {:opaque} find_free_spec(i: nat)
    {
      && i <= |s|
      && forall k:nat | k < i :: s[k].used()
    }

    function method findFree(): (i:nat)
      requires Valid()
      ensures i < 128 ==> !s[i].used()
      ensures find_free_spec(i)
    {
      var f := (e:DirEnt) => !e.used();
      C.find_first_complete(f, s);
      reveal find_free_spec();
      C.find_first(f, s)
    }
  }
  type Dirents = x:preDirents | x.Valid() witness Dirents(C.repeat(DirEnt.zero, 128))
}
