include "dirent.dfy"

module MemDirEntries
{
  import opened Std
  import opened DirEntries
  import opened Machine
  import opened ByteSlice
  import opened FsKinds
  import IntEncoding

  method Pathc?(name: Bytes) returns (p:bool)
    requires name.Valid()
    ensures p == is_pathc(name.data)
  {
    var i: uint64 := 0;
    var len := name.Len();
    if len > 24 {
      return false;
    }
    while i < len
      invariant 0 <= i as nat <= |name.data|
      invariant is_pathc(name.data[..i])
    {
      if name.Get(i) == 0 {
        return false;
      }
      i := i + 1;
    }
    return true;
  }

  datatype MemDirEnt = MemDirEnt(name: Bytes, ino: Ino)
  {
    predicate Valid()
      reads name
    {
      && is_pathc(name.data)
    }

    function val(): DirEnt
      reads name
      requires Valid()
    {
      DirEnt(name.data, ino)
    }

    predicate method used()
    {
      ino as uint64 != 0
    }

    function path(): PathComp
      reads name
      requires Valid()
    {
      name.data
    }

  }

  function mem_dirs_repr(s: seq<MemDirEnt>): set<object>
  {
    set i:nat | i < |s| :: s[i].name
  }

  lemma mem_dirs_repr_app(s1: seq<MemDirEnt>, s2: seq<MemDirEnt>)
    ensures mem_dirs_repr(s1 + s2) == mem_dirs_repr(s1) + mem_dirs_repr(s2)
  {
    forall o:object | o in mem_dirs_repr(s2)
      ensures o in mem_dirs_repr(s1 + s2)
    {
      var i:nat :| i < |s2| && s2[i].name == o;
      assert (s1 + s2)[|s1| + i].name == o;
    }

    forall o:object | o in mem_dirs_repr(s1)
      ensures o in mem_dirs_repr(s1 + s2)
    {
      var i:nat :| i < |s1| && s1[i].name == o;
      assert (s1 + s2)[i].name == o;
    }
  }

  predicate mem_seq_valid(s: seq<MemDirEnt>)
    reads mem_dirs_repr(s)
  {
    forall i:nat | i < |s| :: s[i].Valid()
  }

  function mem_seq_val(s: seq<MemDirEnt>): seq<DirEnt>
    reads mem_dirs_repr(s)
    requires mem_seq_valid(s)
  {
    seq(|s|, (i:nat)
      reads mem_dirs_repr(s)
      requires i < |s|
      requires s[i].Valid() =>
      s[i].val())
  }

  lemma mem_seq_val_app(s1: seq<MemDirEnt>, s2: seq<MemDirEnt>)
    requires mem_seq_valid(s1) && mem_seq_valid(s2)
    ensures mem_seq_val(s1 + s2) == mem_seq_val(s1) + mem_seq_val(s2)
  {}

  method NullTerminatedEqualSmaller(bs1: Bytes, bs2: Bytes) returns (p:bool)
    requires bs1.Valid() && bs2.Valid()
    requires bs1.Len() <= bs2.Len()
    ensures p == (decode_null_terminated(bs1.data) == decode_null_terminated(bs2.data))
  {
    var i: uint64 := 0;
    var len: uint64 := bs1.Len();
    while i < len
      invariant 0 <= i as nat <= |bs1.data|
      invariant bs1.data[..i] == bs2.data[..i]
      invariant decode_null_terminated(bs1.data) == bs1.data[..i] + decode_null_terminated(bs1.data[i..])
      invariant decode_null_terminated(bs2.data) == bs2.data[..i] + decode_null_terminated(bs2.data[i..])

    {
      var b1 := bs1.Get(i);
      var b2 := bs2.Get(i);
      if b1 == 0 || b2 == 0 {
        return b1 == b2;
      }
      assert b1 != 0 && b2 != 0;
      if b1 != b2 {
        assert decode_null_terminated(bs1.data)[i] == b1;
        assert decode_null_terminated(bs2.data)[i] == b2;
        return false;
      }
      i := i + 1;
    }
    if bs1.Len() == bs2.Len() {
      return true;
    }
    assert bs1.Len() < bs2.Len();
    var last := bs2.Get(bs1.Len());
    return last == 0;
  }

  method NullTerminatedEqual(bs1: Bytes, bs2: Bytes) returns (p:bool)
    requires bs1.Valid() && bs2.Valid()
    ensures p == (decode_null_terminated(bs1.data) == decode_null_terminated(bs2.data))
  {
    if bs1.Len() <= bs2.Len() {
      p := NullTerminatedEqualSmaller(bs1, bs2);
      return;
    }
    p := NullTerminatedEqualSmaller(bs2, bs1);
    return;
  }

  method NullTerminatePrefix(bs: Bytes)
    requires bs.Valid()
    modifies bs
    ensures bs.data == decode_null_terminated(old(bs.data))
  {
    var i: uint64 := 0;
    var len: uint64 := bs.Len();
    while i < len
      modifies bs
      invariant i as nat <= |bs.data|
      invariant forall k: nat | k < i as nat :: bs.data[k] != 0
      invariant decode_null_terminated(bs.data) == bs.data[..i] + decode_null_terminated(bs.data[i..])
      invariant bs.data == old(bs.data)
    {
      var b := bs.Get(i);
      if b == 0 {
        bs.Subslice(0, i);
        return;
      }
      i := i + 1;
    }
    return;
  }

  method PadPathc(bs: Bytes)
    modifies bs
    requires is_pathc(bs.data)
    ensures bs.data == encode_pathc(old(bs.data))
  {
    if bs.Len() >= 24 {
      return;
    }
    var zeros := NewBytes(24 - bs.Len());
    bs.AppendBytes(zeros);
  }

  class MemDirents
  {
    ghost var val: Dirents
    const bs: Bytes

    ghost const Repr: set<object> := {this, bs}

    predicate {:opaque} Valid()
      reads Repr
    {
      && bs.data == val.enc()
      && |bs.data| == 4096
    }

    function dir(): Directory
      reads this
    {
      val.dir
    }

    constructor(bs: Bytes, ghost dents: Dirents)
      requires bs.data == dents.enc()
      ensures Valid()
      ensures val == dents
      // for framing
      ensures this.bs == bs
    {
      this.bs := bs;
      this.val := dents;
      new;
      val.enc_len();
      reveal Valid();
    }

    method encode() returns (bs': Bytes)
      requires Valid()
      ensures bs' == bs
      ensures bs'.data == val.enc()
    {
      reveal Valid();
      bs' := bs;
    }

    lemma data_one(k: nat)
      requires Valid()
      requires k < dir_sz
      ensures |bs.data| == 4096
      ensures bs.data[k*32..(k+1) * 32] == val.s[k].enc()
    {
      reveal Valid();
      C.concat_homogeneous_one_list(C.seq_fmap(Dirents.encOne, val.s), k, 32);
    }

    lemma data_one_name(k: nat)
      requires Valid()
      requires k < dir_sz
      ensures |bs.data| == 4096
      ensures bs.data[k*32..k*32+24] == encode_pathc(val.s[k].name)
    {
      reveal Valid();
      data_one(k);
      val.s[k].enc_app();
      assert bs.data[k*32..(k+1)*32][..24] == bs.data[k*32..k*32 + 24];
    }

    lemma data_one_ino(k: nat)
      requires Valid()
      requires k < dir_sz
      ensures |bs.data| == 4096
      ensures bs.data[k*32 + 24..k*32 + 32] == IntEncoding.le_enc64(val.s[k].ino)
    {
      reveal Valid();
      data_one(k);
      val.s[k].enc_app();
      assert bs.data[k*32..(k+1)*32][24..32] == bs.data[k*32 + 24..k*32 + 32];
    }

    twostate lemma data_splice_one(k: nat, v: DirEnt)
      requires old(Valid())
      requires k < dir_sz
      requires (v.enc_len(); reveal Valid(); bs.data == C.splice(old(bs.data), k*32, v.enc()))
      ensures bs.data == C.concat(C.seq_fmap(Dirents.encOne, old(val.s[k := v])))
    {
      reveal Valid();
      v.enc_len();
      C.concat_homogeneous_splice_one(C.seq_fmap(Dirents.encOne, old(val.s)), k as nat, v.enc(), 32);
      //assert bs.data == C.concat(C.seq_fmap(Dirents.encOne, old(val.s))[k as nat := v.enc()]);
      assert C.seq_fmap(Dirents.encOne, old(val.s))[k as nat := v.enc()] ==
             C.seq_fmap(Dirents.encOne, old(val.s)[k as nat := v]);
    }

    method get_ino(k: uint64) returns (ino: Ino)
      requires Valid()
      requires k < 128
      ensures ino == val.s[k].ino
    {
      reveal Valid();
      // we'll prove it's an Ino later, for now it's just a uint64
      var ino': uint64 := IntEncoding.UInt64Get(bs, k*32 + 24);
      data_one_ino(k as nat);
      IntEncoding.lemma_le_enc_dec64(val.s[k].ino);
      ino := ino';
    }

    method get_name(k: uint64) returns (name: Bytes)
      requires Valid()
      requires k < 128
      ensures fresh(name) && name.Valid() && |name.data| == 24
      ensures encode_pathc(val.s[k].name) == name.data
    {
      reveal Valid();
      name := NewBytes(24);
      name.CopyFrom(bs, k*32, 24);
      data_one(k as nat);
      val.s[k].enc_app();
      assert bs.data[k*32..(k+1)*32][..24] == bs.data[k*32..k*32 + 24];
    }

    method get_dirent(k: uint64) returns (r:Option<MemDirEnt>)
      requires Valid()
      requires k < 128
      ensures r.None? ==> !val.s[k].used()
      ensures r.Some? ==>
      && val.s[k].used()
      && fresh(r.x.name)
      && r.x.Valid()
      && r.x.val() == val.s[k]
    {
      var ino := get_ino(k);
      if ino as uint64 == 0 {
        return None;
      }
      var name := get_name(k);
      NullTerminatePrefix(name);
      decode_encode(val.s[k].name);
      return Some(MemDirEnt(name, ino));
    }

    method is_used(k: uint64) returns (p:bool)
      requires Valid()
      requires k < 128
      ensures p == val.s[k].used()
    {
      var ino := get_ino(k);
      p := ino as uint64 != 0;
    }

    method is_name(k: uint64, needle: Bytes) returns (r:Option<Ino>)
      requires Valid()
      requires k < 128
      requires needle.Valid()
      requires is_pathc(needle.data)
      ensures r.None? ==> !(val.s[k].used() && val.s[k].name == needle.data)
      ensures r.Some? ==> val.s[k].used() && val.s[k].name == needle.data && val.s[k].ino == r.x
    {
      var ino := get_ino(k);
      if ino as uint64 == 0 {
        return None;
      }
      var name := get_name(k);
      assert decode_null_terminated(name.data) == val.s[k].name by {
        decode_encode(val.s[k].name);
      }
      decode_nullterm_no_null(needle.data);
      var equal := NullTerminatedEqualSmaller(needle, name);
      if equal {
        return Some(ino);
      } else {
        return None;
      }
    }

    method findFree() returns (free_i: uint64)
      requires Valid()
      ensures free_i as nat == val.findFree()
    {
      var i: uint64 := 0;
      while i < 128
        invariant 0 <= i as nat <= 128
        invariant forall k:nat | k < i as nat :: val.s[k].used()
      {
        var p := is_used(i);
        if !p {
          C.find_first_characterization(Dirents.is_unused, val.s, i as nat);
          return i;
        }
        i := i + 1;
      }
      C.find_first_characterization(Dirents.is_unused, val.s, dir_sz);
      return 128;
    }

    method isEmpty() returns (p:bool)
      requires Valid()
      ensures p == (dir() == map[])
    {
      var i: uint64 := 0;
      while i < 128
        invariant 0 <= i as nat <= 128
        invariant forall k:nat | k < i as nat :: !val.s[k].used()
      {
        var p := is_used(i);
        if p {
          seq_to_dir_present(val.s, i as nat);
          return false;
        }
        i := i + 1;
      }
      none_used_is_empty(val.s);
      return true;
    }

    method findName(name: Bytes) returns (r: Option<(uint64, Ino)>)
      requires Valid()
      requires is_pathc(name.data)
      ensures r.None? ==> name.data !in val.dir && val.findName(name.data) == 128
      ensures r.Some? ==>
      && name.data in val.dir
      && r.x.0 < 128
      && r.x.0 as nat == val.findName(name.data)
      && val.dir[name.data] == r.x.1
    {
      ghost var p: PathComp := name.data;
      var i: uint64 := 0;
      while i < 128
        invariant 0 <= i as nat <= 128
        invariant forall k:nat | k < i as nat :: !(val.s[k].used() && val.s[k].name == p)
      {
        var ino := is_name(i, name);
        if ino.Some? {
          C.find_first_characterization(preDirents.findName_pred(p), val.s, i as nat);
          assert val.findName(p) == i as nat;
          val.findName_found(p);
          return Some( (i, ino.x) );
        }
        i := i + 1;
      }
      C.find_first_characterization(preDirents.findName_pred(p), val.s, dir_sz);
      val.findName_not_found(p);
      return None;
    }

    method usedDents() returns (dents: seq<MemDirEnt>)
      requires Valid()
      ensures mem_seq_valid(dents)
      ensures fresh(mem_dirs_repr(dents))
      ensures seq_to_dir(mem_seq_val(dents)) == val.dir
      ensures |dents| == |val.dir|
    {
      dents := [];
      var i: uint64 := 0;
      while i < 128
        invariant 0 <= i as nat <= 128
        invariant |dents| <= i as nat
        invariant mem_seq_valid(dents)
        invariant fresh(mem_dirs_repr(dents))
        invariant mem_seq_val(dents) == used_dirents(val.s[..i])
      {
        assert val.s[..i+1] == val.s[..i] + [val.s[i]];
        used_dirents_app(val.s[..i], [val.s[i]]);
        var e := get_dirent(i);
        if e.Some? {
          assert val.s[i].used();
          mem_dirs_repr_app(dents, [e.x]);
          assert mem_seq_val(dents + [e.x]) == mem_seq_val(dents) + mem_seq_val([e.x]);
          //assert mem_seq_val([e.x]) == [e.x.val()];
          //assert used_dirents([val.s[i]]) == [val.s[i]];
          //calc {
          //  mem_seq_val(dents + [e.x]);
          //  mem_seq_val(dents) + mem_seq_val([e.x]);
          //  used_dirents(val.s[..i]) + [e.x.val()];
          //}
          dents := dents + [e.x];
        } else {
          assert !val.s[i].used();
          assert used_dirents(val.s[..i+1]) == used_dirents(val.s[..i]);
        }
        i := i + 1;
      }

      assert val.s[..128] == val.s;
      used_dirents_dir(val.s);
      used_dirents_size(val.s);
    }

    static method write_ent(bs: Bytes, k: uint64, ghost v: DirEnt, name: Bytes, ino: Ino)
      modifies bs
      requires k < 128
      requires |bs.data| == 4096
      requires name.data == encode_pathc(v.name) && v.ino == ino
      ensures |v.enc()| == 32
      ensures bs.data == C.splice(old(bs.data), k as nat*32, v.enc())
    {
      v.enc_len();
      v.enc_app();
      bs.CopyTo(k*32, name);
      IntEncoding.UInt64Put(ino, k*32+24, bs);
    }

    method insert_ent(k: uint64, e: MemDirEnt)
      modifies Repr, e.name
      requires Valid() ensures Valid()
      requires e.Valid() && e.used()
      requires k < 128 && k as nat == val.findFree()
      requires val.findName(e.val().name) >= 128
      ensures val.dir == old(val.dir[e.val().name := e.val().ino])
    {
      reveal Valid();
      ghost var v := e.val();
      v.enc_len();
      val.insert_ent_dir(v);
      // modify in place to re-use space
      PadPathc(e.name);
      var padded_name := e.name;
      write_ent(this.bs, k, v, padded_name, e.ino);
      data_splice_one(k as nat, v);
      val := val.insert_ent(k as nat, v);
    }

    method deleteAt(k: uint64)
      modifies Repr
      requires Valid() ensures Valid()
      requires k < 128 && val.s[k].used()
      ensures val.dir == old(map_delete(val.dir, val.s[k].name))
    {
      reveal Valid();
      ghost var old_name := old(val.s[k].name);
      ghost var old_padded_name := bs.data[k*32..k*32 + 24];
      assert old_padded_name == encode_pathc(old_name) by {
        data_one_name(k as nat);
      }

      IntEncoding.UInt64Put(0, k*32 + 24, bs);

      assert bs.data == C.splice(old(bs.data), k as nat * 32,
        old_padded_name + IntEncoding.le_enc64(0));
      // the new entry we're effectively writing (though without actually
      // writing the old name again)
      ghost var e := DirEnt(old_name, 0 as Ino);
      assert old_padded_name + IntEncoding.le_enc64(0) == e.enc() by {
        e.enc_app();
      }
      data_splice_one(k as nat, e);
      val := val.(s := val.s[k as nat := e]);
      seq_to_dir_delete(old(val.s), k as nat, old_name);
    }
  }
}
