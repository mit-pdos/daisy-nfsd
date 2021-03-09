include "../../machine/machine.s.dfy"
include "../../util/std.dfy"
include "../../util/marshal.i.dfy"
include "kinds.dfy"

module DirEntries
{
  import opened Std
  import opened Machine
  import opened ByteSlice
  import opened FsKinds
  import opened Marshal
  import C = Collections

  type String = seq<byte>

  const dirent_sz_u64: uint64 := 64
  const dirent_sz: nat := dirent_sz_u64 as nat
    // dirent_sz - 8
  const path_len_u64: uint64 := 56
  const path_len: nat := path_len_u64 as nat
  const dir_sz_u64: uint64 := 64
  const dir_sz: nat := dir_sz_u64 as nat

  const MAX_FILENAME_SZ: uint64 := path_len_u64

  lemma dirent_sizes_consistent()
    ensures path_len == dirent_sz - 8
    ensures dirent_sz * dir_sz == 4096
  {}

  predicate is_pathc(s: String)
  {
    && |s| <= MAX_FILENAME_SZ as nat
    && forall i | 0 <= i < |s| :: s[i] != 0
  }

  type PathComp = s:String | is_pathc(s)

  function method encode_pathc(pc: PathComp): (s:seq<byte>)
    ensures |s| == path_len
  {
    pc + C.repeat(0 as byte, path_len - |pc|)
  }

  function method decode_null_terminated(s: seq<byte>): String
  {
    if s == [] then []
    else
      if s[0] == 0 as byte then []
      else [s[0]] + decode_null_terminated(s[1..])
  }

  // decode_null_terminated is technically the longest sequence satisfying these properties
  lemma decode_null_terminated_spec(s: seq<byte>)
    ensures C.prefix_of(decode_null_terminated(s), s)
    ensures forall i | 0 <= i < |decode_null_terminated(s)| :: decode_null_terminated(s)[i] != 0
  {}

  function method decode_pathc(s: seq<byte>): PathComp
    requires |s| == path_len
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

  lemma decode_nullterm_null(s: seq<byte>, i: nat)
    requires i < |s| && s[i] == 0
    requires forall k | 0 <= k < i :: s[k] != 0
    ensures decode_null_terminated(s) == s[..i]
  {
    decode_nullterm_prefix(s[..i], s[i..]);
    assert decode_null_terminated(s[i..]) == [];
    assert s == s[..i] + s[i..];
  }

  lemma decode_nullterm_no_null(s: seq<byte>)
    requires forall k | 0 <= k < |s| :: s[k] != 0
    ensures decode_null_terminated(s) == s
  {}

  lemma decode_all_null(count: nat)
    ensures decode_null_terminated(C.repeat(0 as byte, count)) == []
  {}

  lemma decode_encode(pc: PathComp)
    ensures decode_pathc(encode_pathc(pc)) == pc
  {
    decode_nullterm_prefix(pc, C.repeat(0 as byte, path_len - |pc|));
    decode_all_null(path_len - |pc|);
  }

  method DecodeEncodeTest(s: PathComp) returns (s':seq<byte>)
    ensures s' == s
  {
    decode_encode(s);
    s' := decode_pathc(encode_pathc(s));
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

    static predicate method is_used(e: DirEnt) { e.used() }

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
      ensures |enc()| == dirent_sz
    {
      enc_app();
    }

    static lemma zero_enc()
      ensures zero.enc() == C.repeat(0 as byte, dirent_sz)
    {
      zero.enc_app();
      IntEncoding.lemma_enc_0();
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

  function method used_dirents(s: seq<DirEnt>): seq<DirEnt>
  {
    C.seq_filter(DirEnt.is_used, s)
  }

  lemma used_dirents_app(s1: seq<DirEnt>, s2: seq<DirEnt>)
    ensures used_dirents(s1 + s2) == used_dirents(s1) + used_dirents(s2)
  {
    C.seq_filter_app(DirEnt.is_used, s1, s2);
  }

  /*
  lemma {:induction s} used_dirents_unique(s: seq<DirEnt>)
    requires dirents_unique(s)
    ensures dirents_unique(used_dirents(s))
  {
    if s == [] { return; }
    if s[0].used() {
      assert dirents_unique(used_dirents(s[1..]));
      // TODO: need to do this with a forall and line up indices
      return;
    }
    assert used_dirents(s) == used_dirents(s[1..]);
  }
  */

  lemma {:induction s} used_dirents_dir(s: seq<DirEnt>)
    ensures seq_to_dir(s) == seq_to_dir(used_dirents(s))
  {
    if s == [] { return; }
    used_dirents_dir(s[1..]);
    if s[0].used() {
      return;
    }
    assert seq_to_dir(s) == seq_to_dir(s[1..]);
    assert used_dirents(s) == used_dirents(s[1..]);
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

  predicate dirents_unique(s: seq<DirEnt>)
  {
    forall i, j | 0 <= i < |s| && 0 <= j < |s| ::
      s[i].name == s[j].name && s[i].used() && s[j].used() ==> i == j
  }

  lemma seq_to_dir_in_dir(s: seq<DirEnt>, n: PathComp)
    returns (i: nat)
    requires n in seq_to_dir(s)
    ensures i < |s| && s[i].name == n && s[i].used()
  {
    if s == [] { assert false; }
    else {
      if s[0].used() && s[0].name == n {
        i := 0;
      } else {
        var i' := seq_to_dir_in_dir(s[1..], n);
        i := 1 + i';
      }
    }
  }

  lemma seq_to_dir_present(s: seq<DirEnt>, i: nat)
    requires i < |s| && s[i].used()
    requires dirents_unique(s)
    ensures s[i].name in seq_to_dir(s) && seq_to_dir(s)[s[i].name] == s[i].ino
  {
    if s == [] { assert false; }
    else {
      if i == 0 {
      } else {
        seq_to_dir_present(s[1..], i-1);
      }
    }
  }

  lemma seq_to_dir_unique_here(s: seq<DirEnt>)
    requires dirents_unique(s)
    requires 0 < |s| && s[0].used()
    ensures s[0].name !in seq_to_dir(s[1..])
  {
    if s[0].name in seq_to_dir(s[1..]) {
      var i := seq_to_dir_in_dir(s[1..], s[0].name);
    }
  }

  lemma {:induction s, i} seq_to_dir_delete(s: seq<DirEnt>, i: nat, dummy_name: PathComp)
    requires dirents_unique(s)
    requires i < |s| && s[i].used()
    ensures seq_to_dir(s[i := DirEnt(dummy_name, 0 as Ino)]) == map_delete(seq_to_dir(s), s[i].name)
  {
    if 0 < |s| && i == 0 {
      seq_to_dir_unique_here(s);
    }
  }

  lemma {:induction s} seq_to_dir_size(s: seq<DirEnt>)
    requires dirents_unique(s)
    ensures |seq_to_dir(s)| == C.count_matching(DirEnt.is_used, s)
  {
    if s == [] {}
    else {
      seq_to_dir_size(s[1..]);
      var e := s[0];
      if e.used() {
        seq_to_dir_unique_here(s);
        assert |seq_to_dir(s)| == 1 + |seq_to_dir(s[1..])|;
      }
    }
  }

  lemma used_dirents_size(s: seq<DirEnt>)
    requires dirents_unique(s)
    ensures |used_dirents(s)| == |seq_to_dir(s)|
  {
    seq_to_dir_size(s);
    C.seq_filter_size(DirEnt.is_used, s);
  }

  lemma none_used_is_empty(s: seq<DirEnt>)
    requires forall i:nat | i < |s| :: !s[i].used()
    ensures seq_to_dir(s) == map[]
  {}

  datatype preDirents = Dirents(s: seq<DirEnt>)
  {
    static const zero: Dirents := Dirents(C.repeat(DirEnt.zero, dir_sz))

    ghost const dir: Directory := seq_to_dir(s)

    static lemma zero_dir()
      ensures zero.dir == map[]
    {
      seq_to_dir_zeros(dir_sz);
    }

    predicate Valid()
    {
      // 128*32 == 4096 so these will fit in a block
      && |s| == dir_sz
      && dirents_unique(s)
    }

    static function encOne(e: DirEnt): (s:seq<byte>)
      ensures |s| == dirent_sz
    {
      e.enc_len();
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
      C.concat_homogeneous_len(C.seq_fmap(encOne, this.s), dirent_sz);
    }

    static lemma zero_enc()
      ensures zero.enc() == C.repeat(0 as byte, 4096)
    {
      DirEnt.zero_enc();
      assert C.seq_fmap(encOne, zero.s) == C.repeat(DirEnt.zero.enc(), dir_sz);
      C.concat_repeat(0 as byte, dirent_sz, dir_sz);
    }

    function method insert_ent(i: nat, e: DirEnt): (ents': Dirents)
      requires Valid()
      requires i < dir_sz
      requires this.findName(e.name) >= dir_sz
      ensures ents'.Valid()
    {
      var s' := this.s[i := e];
      var ents': preDirents := Dirents(s');
      reveal find_name_spec();
      assert ents'.Valid();
      ents'
    }

    lemma insert_ent_dir(e: DirEnt)
      requires Valid()
      requires this.findName(e.name) >= dir_sz
      requires this.findFree() < dir_sz && e.used()
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

    static function method findName_pred(p: PathComp): DirEnt -> bool
    {
      (e:DirEnt) => e.used() && e.name == p
    }

    function method findName(p: PathComp): (i:nat)
      requires Valid()
      ensures i < dir_sz ==> s[i].used() && s[i].name == p
      ensures find_name_spec(p, i)
    {
      C.find_first_complete(findName_pred(p), s);
      reveal find_name_spec();
      C.find_first(findName_pred(p), s)
    }

    lemma findName_found(p: PathComp)
      requires Valid()
      requires findName(p) < dir_sz
      ensures p in this.dir && this.dir[p] == this.s[findName(p)].ino
    {
      seq_to_dir_present(this.s, findName(p));
    }

    lemma findName_not_found(p: PathComp)
      requires Valid()
      requires findName(p) >= dir_sz
      ensures p !in this.dir
    {
      if p in this.dir {
       var i := seq_to_dir_in_dir(s, p);
       reveal find_name_spec();
      }
    }

    predicate {:opaque} find_free_spec(i: nat)
    {
      && i <= |s|
      && forall k:nat | k < i :: s[k].used()
    }

    static predicate method is_unused(e: DirEnt)
    {
      !e.used()
    }

    function method findFree(): (i:nat)
      requires Valid()
      ensures i < dir_sz ==> !s[i].used()
      ensures find_free_spec(i)
    {
      C.find_first_complete(is_unused, s);
      reveal find_free_spec();
      C.find_first(is_unused, s)
    }

    method deleteAt(i: nat) returns (dents: Dirents)
      requires Valid()
      requires i < dir_sz && s[i].used()
      ensures dents.dir == map_delete(this.dir, s[i].name)
    {
      seq_to_dir_delete(s, i, []);
      var s' := s[i := DirEnt([], 0 as Ino)];
      dents := Dirents(s');
    }

    method usedDents() returns (dents: seq<DirEnt>)
      requires Valid()
      ensures seq_to_dir(dents) == this.dir
      ensures |dents| == |this.dir|
    {
      used_dirents_dir(s);
      used_dirents_size(s);
      dents := used_dirents(this.s);
    }
  }
  type Dirents = x:preDirents | x.Valid() witness Dirents(C.repeat(DirEnt.zero, dir_sz))
}
