include "dirent.dfy"
include "../paths.dfy"
include "../cursor.dfy"

module MemDirEnts
{
  import opened Machine
  import opened ByteSlice
  import opened FsKinds
  import ByteHelpers

  import opened DirEntries
  import opened Paths

  import Inode

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
  import opened JrnlSpec
  import IntEncoding

  import opened MemDirEnts
  import opened DirEntries
  import opened Paths
  import opened FileCursor

  function dirent_off(k: nat): nat
  {
    k * dirent_sz
  }

  function path_ub(k: nat): nat
  {
    k * dirent_sz + path_len
  }

  lemma seq_data_one(data: seq<byte>, val: Dirents, k: nat)
    requires val.enc() == data
    requires k < |val.s|
    ensures data[dirent_off(k)..dirent_off(k+1)] == val.s[k].enc()
  {
    reveal val.enc();
    C.concat_homogeneous_one_list(C.seq_fmap(Dirents.encOne, val.s), k, dirent_sz);
  }

  lemma seq_data_one_name(data: seq<byte>, val: Dirents, k: nat)
    requires val.enc() == data
    requires k < |val.s|
    ensures data[dirent_off(k)..path_ub(k)] == encode_pathc(val.s[k].name)
  {
    seq_data_one(data, val, k);
    val.s[k].enc_app();
    assert data[dirent_off(k)..dirent_off(k+1)][..path_len] ==
      data[dirent_off(k)..path_ub(k)];
  }

  lemma seq_data_one_ino(data: seq<byte>, val: Dirents, k: nat)
    requires val.enc() == data
    requires k < |val.s|
    ensures IntEncoding.le_dec64(data[path_ub(k)..dirent_off(k+1)]) == val.s[k].ino
  {
    seq_data_one(data, val, k);
    val.s[k].enc_app();
    assert data[dirent_off(k)..dirent_off(k+1)][path_len..dirent_sz] ==
      data[path_ub(k)..dirent_off(k+1)];
    assert data[path_ub(k)..dirent_off(k+1)] == IntEncoding.le_enc64(val.s[k].ino);
    IntEncoding.lemma_le_enc_dec64(val.s[k].ino);
  }

  lemma seq_data_splice_one(data: seq<byte>, val: Dirents, k: nat, v: DirEnt)
    returns (val': preDirents)
    requires val.enc() == data
    requires k < |val.s|
    // return this expression for caller's convenience
    ensures val' == Dirents(val.s[k := v])
    ensures (v.enc_len();
    C.splice(data, k*dirent_sz, v.enc()) == val'.enc())
  {
    v.enc_len();
    C.concat_homogeneous_splice_one(C.seq_fmap(Dirents.encOne, val.s),
      k as nat, v.enc(), dirent_sz);
    //assert data == C.concat(C.seq_fmap(Dirents.encOne, val.s)[k as nat := v.enc()]);
    assert C.seq_fmap(Dirents.encOne, val.s)[k as nat := v.enc()] ==
            C.seq_fmap(Dirents.encOne, val.s[k as nat := v]);
    val' := Dirents(val.s[k := v]);
    reveal val'.enc();
  }

  lemma seq_data_splice_ino(data: seq<byte>, val: Dirents, k: nat, ino': Ino)
    returns (val': preDirents)
    requires val.enc() == data
    requires k < |val.s|
    ensures val' == Dirents(val.s[k := val.s[k].(ino := ino')])
    ensures
    C.splice(data, k*dirent_sz + path_len, IntEncoding.le_enc64(ino')) == val'.enc()
  {
    var old_name := val.s[k].name;
    var old_padded_name := data[dirent_off(k)..path_ub(k)];
    assert old_padded_name == encode_pathc(old_name) by {
      seq_data_one_name(data, val, k);
    }
    var e' := val.s[k].(ino := ino');
    e'.enc_app();
    // splicing in just the inode encoding is like splicing in the encoding of the new entry
    assert C.splice(data, k*dirent_sz + path_len, IntEncoding.le_enc64(ino')) ==
      C.splice(data, k*dirent_sz, e'.enc());
    val' := seq_data_splice_one(data, val, k, e');
  }

  class MemDirents
  {
    ghost var val: Dirents
    const file: Cursor

    function Repr(): set<object>
      reads this.file
    {
        {this} + file.Repr()
    }

    predicate {:opaque} ValidCore()
      requires file.fs.ValidDomains()
      reads this, file.fs
    {
      && file.contents() == val.enc()
    }

    predicate {:opaque} ValidVal()
      reads this
    {
      && |val.s| <= dir_sz
      && |val.s| % 64 == 0
    }

    predicate {:opaque} Valid()
      reads Repr(), file.ReprFs
    {
      && file.Valid()
      && ValidCore()
      && ValidVal()
    }

    function dir(): Directory
      reads this
    {
      val.dir
    }

    constructor(file: Cursor, ghost dents: Dirents)
      requires file.Valid()
      requires file.contents() == dents.enc()
      requires |file.contents()| % 4096 == 0
      ensures Valid()
      ensures val == dents
      ensures this.file == file
    {
      this.file := file;
      this.val := dents;
      new;
      reveal ValidCore();
      reveal ValidVal();
      reveal Valid();
    }

    static function dir_blk(k: nat): nat
    {
        k / 64 * 4096
    }

    // offset of a whole-file offset within one paged-in block in the cursor
    static function dir_blk_off(k: nat): nat
    {
        k % 64
    }

    predicate at_dir_off(k: nat)
      reads this, file
    {
      && k < |val.s|
      && file.off as nat == dir_blk(k)
      && file.valid?
    }

    predicate has_jrnl(txn: Txn)
      reads file.fs.Repr
    {
      file.fs.has_jrnl(txn)
    }

    predicate inode_unchanged()
      reads file.fs.fs.fs.fs, file.i.Repr
    {
      && file.i.Valid()
      && file.fs.inode_unchanged(file.ino, file.i.val())
    }

    method finishReadonly()
      modifies file.fs.fs.fs.fs
      requires Valid()
      requires inode_unchanged()
      ensures file.fs.Valid()
    {
      reveal Valid();
      reveal file.ValidFs();
      file.fs.finishInodeReadonly(file.ino, file.i);
    }

    method finish(txn: Txn)
      modifies file.ReprFs
      requires has_jrnl(txn)
      requires Valid()
      ensures file.fs.Valid()
      ensures file.fs.types_unchanged()
      ensures file.fs.data == old(file.fs.data)
    {
      reveal Valid();
      reveal file.ValidFs();
      file.fs.finishInode(txn, file.ino, file.i);
    }

    method loadDirOff(txn: Txn, k: uint64)
      modifies file
      requires Valid() ensures Valid()
      requires has_jrnl(txn)
      requires k as nat < |val.s|
      ensures at_dir_off(k as nat)
      ensures file.buffer_fresh()
    {
      reveal Valid();
      reveal ValidCore();
      file.advanceTo(txn, k / 64 * 4096);
    }

    lemma file_data(k: nat)
      requires Valid()
      requires at_dir_off(k)
      ensures |val.s| % 64 == 0
      ensures file.has_data(val.enc()[dir_blk(k) .. dir_blk(k) + 4096])
    {
      reveal Valid();
      reveal ValidCore();
      reveal ValidVal();
      file.data_ok();
    }

    // internal method to give well-formedness
    lemma reveal_fs_dom()
      requires Valid()
      ensures file.fs.ValidDomains()
    {
      reveal Valid();
    }

    // we need this invariant, so help caller maintain it
    lemma fs_ino_size()
      requires Valid()
      ensures (reveal_fs_dom(); |file.fs.data[file.ino]| % 4096 == 0)
    {
      reveal Valid();
      reveal ValidCore();
      reveal ValidVal();
    }

    lemma fs_valid_ino()
      requires Valid()
      ensures file.fs.ValidIno(file.ino, file.i)
    {
      reveal Valid();
      reveal file.ValidFs();
    }

    // give the caller the right double-subslice fact
    lemma file_subslice(k: nat, start: nat, end: nat)
      requires Valid()
      requires at_dir_off(k)
      requires start <= end <= 4096
      ensures |file.bs.data| == 4096
      ensures (reveal_fs_dom();
      && dir_blk(k) + end <= |file.contents()|
      && file.bs.data[start..end] ==
        file.contents()[dir_blk(k) + start .. dir_blk(k) + end])
    {
      reveal Valid();
      file.data_ok();
      C.double_subslice_auto(file.fs.data[file.ino]);
    }

    method get_ino(txn: Txn, k: uint64) returns (ino: Ino)
      modifies file
      requires Valid() ensures Valid()
      requires has_jrnl(txn)
      requires k as nat < |val.s|
      ensures ino == val.s[k].ino
      ensures file.buffer_fresh()
    {
      reveal Valid();
      reveal ValidCore();
      loadDirOff(txn, k);
      var off: uint64 := (k%64) * dirent_sz_u64 + path_len_u64;
      file_subslice(k as nat, off as nat, off as nat + 8);
      // we'll prove it's an Ino later, for now it's just a uint64
      var ino': uint64 := IntEncoding.UInt64Get(file.bs, off);
      seq_data_one_ino(file.contents(), val, k as nat);
      ino := ino';
    }

    method get_name(txn: Txn, k: uint64) returns (name: Bytes)
      modifies file
      requires Valid() ensures Valid()
      requires has_jrnl(txn)
      requires k as nat < |val.s|
      // since file.bs could also change, need to promise that it doesn't change
      // to become name
      ensures name != file.bs && fresh(name) && |name.data| == path_len
      ensures encode_pathc(val.s[k].name) == name.data
      ensures file.buffer_fresh()
    {
      reveal Valid();
      reveal ValidCore();
      loadDirOff(txn, k);
      name := NewBytes(path_len_u64);
      var start := (k%64) * dirent_sz_u64;
      file_subslice(k as nat, start as nat, start as nat + path_len);
      ByteHelpers.CopyFrom(name, file.bs, start, path_len_u64);
      seq_data_one_name(file.contents(), val, k as nat);
    }

    method get_dirent(txn: Txn, k: uint64) returns (r:Option<MemDirEnt>)
      modifies file
      requires Valid() ensures Valid()
      requires has_jrnl(txn)
      requires k as nat < |val.s|
      ensures r.None? ==> !val.s[k].used()
      ensures r.Some? ==>
      && val.s[k].used()
      && fresh(r.x.name)
      && r.x.Valid()
      && r.x.val() == val.s[k]
      ensures file.buffer_fresh()
    {
      reveal Valid();
      var ino := get_ino(txn, k);
      if ino as uint64 == 0 {
        return None;
      }
      var name := get_name(txn, k);
      NullTerminatePrefix(name);
      decode_encode(val.s[k].name);
      return Some(MemDirEnt(name, ino));
    }

    method is_used(txn: Txn, k: uint64) returns (p:bool)
      modifies file
      requires Valid() ensures Valid()
      requires has_jrnl(txn)
      requires k as nat < |val.s|
      ensures p == val.s[k].used()
      ensures file.buffer_fresh()
    {
      var ino := get_ino(txn, k);
      p := ino as uint64 != 0;
    }

    method is_name(txn: Txn, k: uint64, needle: Bytes) returns (r:Option<Ino>)
      modifies file
      requires Valid() ensures Valid()
      requires has_jrnl(txn)
      requires k as nat < |val.s|
      requires needle.Valid()
      requires is_pathc(needle.data)
      ensures r.None? ==> !(val.s[k].used() && val.s[k].name == needle.data)
      ensures r.Some? ==> val.s[k].used() && val.s[k].name == needle.data && val.s[k].ino == r.x
      ensures file.buffer_fresh()
    {
      var ino := get_ino(txn, k);
      if ino as uint64 == 0 {
        return None;
      }
      var name := get_name(txn, k);
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

    method dirSize() returns (num: uint64)
      requires Valid()
      ensures num as nat == |val.s|
    {
      reveal Valid();
      var sz := file.size();
      num := sz / 64;
      reveal ValidCore();
    }

    method findFree(txn: Txn) returns (free_i: uint64)
      modifies file
      requires Valid() ensures Valid()
      requires has_jrnl(txn)
      ensures free_i as nat == val.findFree()
      ensures file.buffer_fresh()
    {
      reveal Valid();
      var num_ents := dirSize();
      var i: uint64 := 0;
      while i < num_ents
        invariant Valid()
        invariant file.buffer_fresh()
        invariant 0 <= i as nat <= |val.s|
        invariant forall k:nat | k < i as nat :: val.s[k].used()
      {
        var p := is_used(txn, i);
        if !p {
          C.find_first_characterization(Dirents.is_unused, val.s, i as nat);
          return i;
        }
        i := i + 1;
      }
      C.find_first_characterization(Dirents.is_unused, val.s, |val.s|);
      return num_ents;
    }

    method isEmpty(txn: Txn) returns (p:bool)
      modifies file
      requires Valid() ensures Valid()
      requires has_jrnl(txn)
      ensures p == (dir() == map[])
      ensures file.buffer_fresh()
    {
      var num_ents := dirSize();
      var i: uint64 := 0;
      while i < num_ents
        invariant Valid()
        invariant file.buffer_fresh()
        invariant 0 <= i as nat <= |val.s|
        invariant forall k:nat | k < i as nat :: !val.s[k].used()
      {
        var p := is_used(txn, i);
        if p {
          seq_to_dir_present(val.s, i as nat);
          return false;
        }
        i := i + 1;
      }
      none_used_is_empty(val.s);
      return true;
    }

    method findName(txn: Txn, name: Bytes) returns (r: Option<(uint64, Ino)>)
      modifies file
      requires Valid() ensures Valid()
      requires has_jrnl(txn)
      requires is_pathc(name.data)
      ensures r.None? ==> name.data !in val.dir && val.findName(name.data) == |val.s|
      ensures r.Some? ==>
      && name.data in val.dir
      && r.x.0 as nat < |val.s|
      && r.x.0 as nat == val.findName(name.data)
      && val.dir[name.data] == r.x.1
      ensures fresh(Repr() - old(Repr()))
    {
      ghost var p: PathComp := name.data;
      var num_ents := dirSize();
      var i: uint64 := 0;
      while i < num_ents
        invariant Valid()
        invariant file.buffer_fresh()
        invariant 0 <= i as nat <= |val.s|
        invariant forall k:nat | k < i as nat :: !(val.s[k].used() && val.s[k].name == p)
      {
        reveal is_pathc();
        var ino := is_name(txn, i, name);
        if ino.Some? {
          C.find_first_characterization(preDirents.findName_pred(p), val.s, i as nat);
          assert val.findName(p) == i as nat;
          val.findName_found(p);
          return Some( (i, ino.x) );
        }
        i := i + 1;
      }
      C.find_first_characterization(preDirents.findName_pred(p), val.s, |val.s|);
      val.findName_not_found(p);
      return None;
    }

    method usedDents(txn: Txn) returns (dents: seq<MemDirEnt>)
      modifies file
      requires Valid() ensures Valid()
      requires has_jrnl(txn)
      ensures mem_seq_valid(dents)
      ensures fresh(mem_dirs_repr(dents))
      ensures seq_to_dir(mem_seq_val(dents)) == val.dir
      ensures |dents| == |val.dir|
    {
      dents := [];
      var num_ents := dirSize();
      var i: uint64 := 0;
      while i < num_ents
        invariant Valid()
        invariant 0 <= i as nat <= |val.s|
        invariant |dents| <= i as nat
        invariant mem_seq_valid(dents)
        invariant fresh(mem_dirs_repr(dents))
        invariant mem_seq_val(dents) == used_dirents(val.s[..i])
      {
        assert val.s[..i+1] == val.s[..i] + [val.s[i]];
        used_dirents_app(val.s[..i], [val.s[i]]);
        var e := get_dirent(txn, i);
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

      assert val.s[..|val.s|] == val.s;
      used_dirents_dir(val.s);
      used_dirents_size(val.s);
    }

    static method write_ent(bs: Bytes, k: uint64, ghost v: DirEnt, name: Bytes, ino: Ino)
      modifies bs
      requires k as nat < 64
      requires |bs.data| == 4096
      requires name.data == encode_pathc(v.name) && v.ino == ino
      ensures |v.enc()| == dirent_sz
      ensures bs.data == C.splice(old(bs.data), k as nat*dirent_sz, v.enc())
    {
      v.enc_app();
      ByteHelpers.CopyTo(bs, k*dirent_sz_u64, name);
      IntEncoding.UInt64Put(ino, k*dirent_sz_u64 + path_len_u64, bs);
    }

    method insertEnt(txn: Txn, k: uint64, e: MemDirEnt)
      returns (ok:bool)
      modifies Repr(), file.ReprFs
      requires Valid() ensures ok ==> Valid()
      requires has_jrnl(txn)
      requires e.name != file.bs
      requires e.Valid() && e.used()
      requires k as nat < |val.s| && k as nat == val.findFree()
      requires val.findName(e.val().name) >= |val.s|
      ensures file.fs.types_unchanged()
      ensures ok ==> val.dir == old(val.dir[e.val().name := e.val().ino])
      ensures ok ==> file.fs.data == old(file.fs.data)[file.ino := val.enc()]
    {
      reveal Valid();
      reveal ValidCore();
      ghost var v := e.val();
      v.enc_len();
      val.insert_ent_dir(v);
      ghost var val' := seq_data_splice_one(file.contents(), val, k as nat, v);

      loadDirOff(txn, k);
      file_data(k as nat);
      var padded_name := PaddedPathc(e.name);
      assert |file.bs.data| == 4096 by {
        reveal file.ValidBytes();
      }
      write_ent(file.bs, k % 64, v, padded_name, e.ino);
      assert file.ValidFs() by {
        reveal file.ValidFs();
      }
      ok := file.writeback(txn);
      val := val';
      C.double_splice_auto(old(file.contents()));
      assert ok ==> Valid() by { reveal ValidVal(); }
      assert ok ==> file.fs.data[file.ino] == val.enc();
    }

    method deleteAt(txn: Txn, k: uint64)
      returns (ok: bool)
      modifies Repr(), file.ReprFs
      requires Valid() ensures ok ==> Valid()
      requires has_jrnl(txn)
      requires k as nat < |val.s| && val.s[k].used()
      ensures file.fs.types_unchanged()
      ensures ok ==> val.dir == old(map_delete(val.dir, val.s[k].name))
      ensures ok ==> file.fs.data == old(file.fs.data)[file.ino := val.enc()]
    {
      reveal Valid();
      reveal ValidCore();
      ghost var old_name := val.s[k].name;
      ghost var old_file := file.contents();

      loadDirOff(txn, k);
      file_data(k as nat);

      var put_off := (k%64)*dirent_sz_u64 + path_len_u64;
      IntEncoding.UInt64Put(0, put_off, file.bs);

      assert file.ValidFs() by {
        reveal file.ValidFs();
      }
      ok := file.writeback(txn);
      if !ok {
        return;
      }
      reveal dirents_unique();
      ghost var val' := seq_data_splice_ino(old_file, val, k as nat, 0 as Ino);
      val := val';

      seq_to_dir_delete(old(val.s), k as nat, old_name);
      assert file.fs.data[file.ino] == val.enc() by {
        C.double_splice(old(file.contents()),
          dir_blk(k as nat), dir_blk(k as nat) + 4096,
          (k as nat % 64)*dirent_sz + path_len, IntEncoding.le_enc64(0 as uint64));
      }
      assert Valid() by {
        assert ValidCore();
        reveal ValidVal();
      }
    }

    method grow(txn: Txn)
      returns (ok: bool)
      modifies Repr(), file.ReprFs
      requires Valid() ensures ok ==> Valid()
      requires has_jrnl(txn)
      requires val.findFree() >= |val.s|
      ensures file.fs.types_unchanged()
      ensures val.dir == old(val.dir)
      ensures fresh(file.Repr() - old(file.Repr()))
      ensures ok ==>
      && old(|val.s| + 64 <= dir_sz)
      && val == old(val.extend_zero(64))
      && val.findFree() == old(val.findFree())
      && val.findFree() < |val.s|
      && file.fs.data == old(file.fs.data)[file.ino := val.enc()]
    {
      reveal Valid();
      assert val.findFree() == |val.s| by {
        reveal val.find_free_spec();
      }
      var sz := file.size();
      if sz >= 64*dir_sz_u64 {
        print "directory ", file.ino, " cannot be grown further\n";
        ok := false;
        return;
      }
      assert |val.s|+64 <= dir_sz by {
        reveal ValidCore();
        reveal ValidVal();
      }
      ok := file.grow(txn);
      if !ok {
        return;
      }
      reveal ValidCore();
      val.extend_zero_has_free(64);
      val := val.extend_zero(64);
      assert |val.s| == old(|val.s| + 64);
      assert Valid() by {
        assert ValidCore();
        assert file.Valid();
        assert ValidVal() by {
          reveal ValidVal();
          Arith.mod_add_modulus(old(|val.s|), 64);
        }
      }
    }

    method getAttrs() returns (attrs: Inode.Attrs)
      requires Valid()
      ensures && file.ino in file.fs.types
              && attrs == file.fs.types[file.ino]
    {
      reveal Valid();
      attrs := file.getAttrs();
    }

    method setAttrs(attrs': Inode.Attrs)
      modifies file.ReprFs
      requires Valid() ensures Valid()
      requires file.ino in file.fs.types &&
               attrs'.ty == file.fs.types[file.ino].ty
      ensures file.fs.types == old(file.fs.types[file.ino := attrs'])
      ensures val == old(val)
      ensures fresh(file.Repr() - old(file.Repr()))
      ensures file.fs.data == old(file.fs.data)
    {
      reveal Valid();
      file.setAttrs(attrs');
      assert ValidCore() by { reveal ValidCore(); }
    }

  }
}
