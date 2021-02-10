include "fs.dfy"

module IndFs
{
  import opened Machine
  import opened ByteSlice
  import opened FsKinds
  import opened JrnlSpec
  import opened Fs
  import opened Marshal
  import C = Collections

  predicate block_has_blknos(b: Block, blknos: seq<Blkno>)
  {
    && is_block(b)
    && b == seq_enc_uint64(blknos)
    && |blknos| == 512
  }

  // there are two redundant length expressions in block_has_blknos, we can use
  // either of them to prove block_has_blknos
  lemma block_has_blknos_len(b: Block, blknos: seq<Blkno>)
    requires b == seq_enc_uint64(blknos)
    requires is_block(b) || |blknos| == 512
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
    ensures block_has_blknos(bs.data, blknos)
  {
    var enc := new Encoder(4096);
    enc.PutInts(blknos);
    assert enc.enc == C.seq_fmap(encUInt64, blknos);
    enc.is_complete();
    bs := enc.Finish();
    return;
  }

  method decode_blknos(bs: Bytes, ghost blknos: seq<Blkno>) returns (blknos': seq<Blkno>)
    requires block_has_blknos(bs.data, blknos)
    ensures blknos' == blknos
  {
    var dec := new Decoder.Init(bs, C.seq_fmap(encUInt64, blknos));
    assert dec.enc[..512] == dec.enc;
    blknos' := dec.GetInts(512, blknos);
    return;
  }

  datatype Idx = direct(k: nat) | indirect(k: nat, m: nat)
  {
    predicate Valid()
    {
      match this {
        case direct(k) => k < 10
        case indirect(k, m) => k < 5 && m < 512
      }
    }

    function flat(): nat
      requires Valid()
    {
      match this {
        case direct(k) => k
        case indirect(k, m) => 10 + k * 512 + m
      }
    }

    static function from_flat(n: nat): (i:Idx)
      requires n < 10 + 5*512
      ensures i.Valid()
    {
      if n < 10 then
        direct(n)
      else (
        var x := n-10;
        indirect(x/512, x % 512)
      )
    }

    lemma to_from_flat()
      requires Valid()
      ensures from_flat(this.flat()) == this
    {}

    static lemma from_to_flat(n: nat)
      requires n < 10 + 5*512
      ensures from_flat(n).flat() == n
    {}
  }

  datatype IndBlock = IndBlock(bn: Blkno, blknos: seq<Blkno>)
  {
    static const zero: IndBlock := IndBlock(0, C.repeat(0 as Blkno, 512))

    predicate Valid()
    {
      && blkno_ok(bn)
      && |blknos| == 512
      && (forall k: int | 0 <= k < 512 :: blkno_ok(blknos[k]))
    }

    static lemma zero_ok()
      ensures zero.Valid()
    {}

    static lemma zero_in_fs(fs: Filesys)
      requires fs.Valid()
      ensures zero.in_fs(fs)
    {
      zero_block_blknos();
    }

    predicate in_fs(fs: Filesys)
      reads fs.Repr()
      requires fs.Valid()
      requires Valid()
    {
      var b := zero_lookup(fs.data_block, this.bn);
      && block_has_blknos(b, this.blknos)
    }
  }

  datatype IndInodeData = IndInodeData(sz: nat, blks: seq<Block>)
  {
    static const zero: IndInodeData := IndInodeData(0, C.repeat(block0, 10 + 5*512))

    predicate Valid()
    {
      && sz <= Inode.MAX_SZ
      && |blks| == 10 + 5 * 512
    }

    static lemma zero_valid()
      ensures zero.Valid()
    {}
  }

  class IndFilesys
  {
    ghost var ino_meta: map<Ino, seq<IndBlock>>
    ghost var ino_data: map<Ino, IndInodeData>
    const fs: Filesys

    function Repr(): set<object>
    {
      {this} + fs.Repr()
    }

    static predicate meta_valid?(meta: seq<IndBlock>)
    {
      && |meta| == 5
      && (forall k: nat | k < 5 :: meta[k].Valid())
    }

    predicate ValidMeta()
      reads this
    {
      && ino_dom(ino_meta)
      && (forall ino | ino_ok(ino) :: meta_valid?(ino_meta[ino]))
    }

    predicate ValidData()
      reads this
    {
      && ino_dom(ino_data)
      && (forall ino | ino_ok(ino) :: ino_data[ino].Valid())
    }

    static predicate ino_ind_match?(d: InodeData, meta: seq<IndBlock>, id: IndInodeData, data_block: map<Blkno, Block>)
      requires blkno_dom(data_block)
      requires meta_valid?(meta)
      requires id.Valid()
    {
      && d.Valid()
      && id.sz == d.sz
      && forall idx: Idx | idx.Valid() ::
      (match idx {
        case direct(k) => d.blks[k] == id.blks[idx.flat()]
        case indirect(k, m) =>
          zero_lookup(data_block, meta[k].blknos[m]) == id.blks[idx.flat()]
      })
    }

    predicate {:opaque} Valid_ino_data()
      reads this.Repr()
      requires fs.Valid()
      requires ino_dom(ino_meta)
      requires ino_dom(ino_data)
      requires ValidMeta()
      requires ValidData()
    {
      forall ino | ino_ok(ino) ::
        ino_ind_match?(fs.inode_blks[ino], ino_meta[ino], ino_data[ino], fs.data_block)
    }

    predicate Valid()
      reads this.Repr()
    {
      && fs.Valid()
      && ValidMeta()
      && ValidData()
    }

    constructor(d: Disk)
      ensures Valid()
    {
      this.fs := new Filesys.Init(d);
      this.ino_meta := map ino: Ino | ino_ok(ino) :: C.repeat(IndBlock.zero, 5);
      this.ino_data := map ino: Ino | ino_ok(ino) :: IndInodeData.zero;
      IndInodeData.zero_valid();
    }
  }

}
