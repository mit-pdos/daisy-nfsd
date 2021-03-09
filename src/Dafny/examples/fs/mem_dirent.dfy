include "dirent.dfy"
include "paths.dfy"

module MemDirEnts
{
  import opened Machine
  import opened ByteSlice
  import opened FsKinds

  import opened DirEntries
  import opened Paths

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
}

module MemDirEntries
{
  import opened Std
  import opened Machine
  import opened ByteSlice
  import opened FsKinds
  import IntEncoding

  import opened MemDirEnts
  import opened DirEntries
  import opened Paths

  class MemDirents
  {
    ghost var val: Dirents
    const bs: Bytes

    ghost const Repr: set<object> := {this, bs}

    predicate {:opaque} ValidCore()
      reads Repr
    {
      && bs.data == val.enc()
      && |bs.data| == 4096
    }

    predicate Valid()
      reads Repr
    {
      && ValidCore()
      && |val.s| == dir_sz
    }

    function dir(): Directory
      reads this
    {
      val.dir
    }

    constructor(bs: Bytes, ghost dents: Dirents)
      requires bs.data == dents.enc()
      requires |dents.s| == dir_sz
      ensures Valid()
      ensures val == dents
      // for framing
      ensures this.bs == bs
    {
      this.bs := bs;
      this.val := dents;
      new;
      val.enc_len();
      reveal ValidCore();
    }

    method encode() returns (bs': Bytes)
      requires Valid()
      ensures bs' == bs
      ensures bs'.data == val.enc()
    {
      reveal ValidCore();
      bs' := bs;
    }

    static predicate dir_off?(k: uint64)
    {
      k as nat < dir_sz
    }

    static function dirent_off(k: nat): nat
    {
      k * dirent_sz
    }

    static function dirent_off_u64(k: uint64): uint64
      requires dir_off?(k)
    {
      k * dirent_sz_u64
    }

    static function path_ub(k: nat): nat
    {
      k * dirent_sz + path_len
    }

    lemma data_one(k: nat)
      requires Valid()
      requires k < dir_sz
      ensures |bs.data| == 4096
      ensures bs.data[dirent_off(k)..dirent_off(k+1)] == val.s[k].enc()
    {
      reveal ValidCore();
      C.concat_homogeneous_one_list(C.seq_fmap(Dirents.encOne, val.s), k, dirent_sz);
    }

    lemma data_one_name(k: nat)
      requires Valid()
      requires k < dir_sz
      ensures |bs.data| == 4096
      ensures bs.data[dirent_off(k)..path_ub(k)] == encode_pathc(val.s[k].name)
    {
      reveal ValidCore();
      data_one(k);
      val.s[k].enc_app();
      assert bs.data[dirent_off(k)..dirent_off(k+1)][..path_len] ==
        bs.data[dirent_off(k)..path_ub(k)];
    }

    lemma data_one_ino(k: nat)
      requires Valid()
      requires k < dir_sz
      ensures |bs.data| == 4096
      ensures bs.data[path_ub(k)..dirent_off(k+1)] == IntEncoding.le_enc64(val.s[k].ino)
    {
      reveal ValidCore();
      data_one(k);
      val.s[k].enc_app();
      assert bs.data[dirent_off(k)..dirent_off(k+1)][path_len..dirent_sz] ==
        bs.data[path_ub(k)..dirent_off(k+1)];
    }

    twostate lemma data_splice_one(k: nat, v: DirEnt)
      requires old(Valid())
      requires k < dir_sz
      requires (v.enc_len(); reveal ValidCore();
                bs.data == C.splice(old(bs.data), k*dirent_sz, v.enc()))
      ensures bs.data == C.concat(C.seq_fmap(Dirents.encOne, old(val.s[k := v])))
    {
      reveal ValidCore();
      v.enc_len();
      C.concat_homogeneous_splice_one(C.seq_fmap(Dirents.encOne, old(val.s)),
        k as nat, v.enc(), dirent_sz);
      //assert bs.data == C.concat(C.seq_fmap(Dirents.encOne, old(val.s))[k as nat := v.enc()]);
      assert C.seq_fmap(Dirents.encOne, old(val.s))[k as nat := v.enc()] ==
             C.seq_fmap(Dirents.encOne, old(val.s)[k as nat := v]);
    }

    method get_ino(k: uint64) returns (ino: Ino)
      requires Valid()
      requires dir_off?(k)
      ensures ino == val.s[k].ino
    {
      reveal ValidCore();
      // we'll prove it's an Ino later, for now it's just a uint64
      var ino': uint64 := IntEncoding.UInt64Get(bs, k*dirent_sz_u64 + path_len_u64);
      data_one_ino(k as nat);
      IntEncoding.lemma_le_enc_dec64(val.s[k].ino);
      ino := ino';
    }

    method get_name(k: uint64) returns (name: Bytes)
      requires Valid()
      requires dir_off?(k)
      ensures fresh(name) && name.Valid() && |name.data| == path_len
      ensures encode_pathc(val.s[k].name) == name.data
    {
      reveal ValidCore();
      name := NewBytes(path_len_u64);
      name.CopyFrom(bs, k*dirent_sz_u64, path_len_u64);
      data_one(k as nat);
      val.s[k].enc_app();
      assert bs.data[dirent_off(k as nat)..dirent_off(k as nat+1)][..path_len] ==
        bs.data[dirent_off(k as nat)..path_ub(k as nat)];
    }

    method get_dirent(k: uint64) returns (r:Option<MemDirEnt>)
      requires Valid()
      requires dir_off?(k)
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
      requires dir_off?(k)
      ensures p == val.s[k].used()
    {
      var ino := get_ino(k);
      p := ino as uint64 != 0;
    }

    method is_name(k: uint64, needle: Bytes) returns (r:Option<Ino>)
      requires Valid()
      requires dir_off?(k)
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
      while i < dir_sz_u64
        invariant 0 <= i as nat <= dir_sz
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
      return dir_sz_u64;
    }

    method isEmpty() returns (p:bool)
      requires Valid()
      ensures p == (dir() == map[])
    {
      var i: uint64 := 0;
      while i < dir_sz_u64
        invariant 0 <= i as nat <= dir_sz
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
      ensures r.None? ==> name.data !in val.dir && val.findName(name.data) == dir_sz
      ensures r.Some? ==>
      && name.data in val.dir
      && dir_off?(r.x.0)
      && r.x.0 as nat == val.findName(name.data)
      && val.dir[name.data] == r.x.1
    {
      ghost var p: PathComp := name.data;
      var i: uint64 := 0;
      while i < dir_sz_u64
        invariant 0 <= i as nat <= dir_sz
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
      while i < dir_sz_u64
        invariant 0 <= i as nat <= dir_sz
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

      assert val.s[..dir_sz] == val.s;
      used_dirents_dir(val.s);
      used_dirents_size(val.s);
    }

    static method write_ent(bs: Bytes, k: uint64, ghost v: DirEnt, name: Bytes, ino: Ino)
      modifies bs
      requires dir_off?(k)
      requires |bs.data| == 4096
      requires name.data == encode_pathc(v.name) && v.ino == ino
      ensures |v.enc()| == dirent_sz
      ensures bs.data == C.splice(old(bs.data), k as nat*dirent_sz, v.enc())
    {
      v.enc_len();
      v.enc_app();
      bs.CopyTo(k*dirent_sz_u64, name);
      IntEncoding.UInt64Put(ino, k*dirent_sz_u64 + path_len_u64, bs);
    }

    method insert_ent(k: uint64, e: MemDirEnt)
      modifies Repr, e.name
      requires Valid() ensures Valid()
      requires e.Valid() && e.used()
      requires dir_off?(k) && k as nat == val.findFree()
      requires val.findName(e.val().name) >= dir_sz
      ensures val.dir == old(val.dir[e.val().name := e.val().ino])
    {
      reveal ValidCore();
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
      requires dir_off?(k) && val.s[k].used()
      ensures val.dir == old(map_delete(val.dir, val.s[k].name))
    {
      reveal ValidCore();
      ghost var old_name := old(val.s[k].name);
      ghost var old_padded_name := bs.data[dirent_off(k as nat)..path_ub(k as nat)];
      assert old_padded_name == encode_pathc(old_name) by {
        data_one_name(k as nat);
      }

      IntEncoding.UInt64Put(0, k*dirent_sz_u64 + path_len_u64, bs);

      assert bs.data == C.splice(old(bs.data), k as nat * dirent_sz,
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
