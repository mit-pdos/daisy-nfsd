#!/usr/bin/env python3

from timing import get_name, get_time, parse_df


def test_name_parse():
    line = r"""Verifying CheckWellformed$$_26_Inode.__default.blks__unique ..."""
    d = get_name(line)
    assert d is not None
    assert d["type"] == "CheckWellformed"
    assert d["name"] == "__default.blks__unique"


def test_timing_parse1():
    line = r"""  [0.409 s, 1 proof obligation]  verified"""
    d = get_time(line)
    assert d is not None
    assert d["time_s"] == 0.409
    assert d["obligations"] == 1
    assert d["result"] == "ok"


def test_timing_parse2():
    line = r"""  [0.360 s, 50 proof obligations]  verified"""
    d = get_time(line)
    assert d is not None
    assert d["time_s"] == 0.360
    assert d["obligations"] == 50


def test_timing_parse3():
    line = r"""  [60.987 s, 161 proof obligations]  timed out"""
    d = get_time(line)
    assert d is not None
    assert d["time_s"] == 60.987
    assert d["result"] == "timeout"


def test_df_parse():
    lines = r"""
Verifying CheckWellformed$$_26_Inode.__default.encode__ino ...
  [0.128 s, 1 proof obligation]  verified

Verifying Impl$$_26_Inode.__default.encode__ino ...
  [0.360 s, 50 proof obligations]  verified

Verifying CheckWellformed$$_26_Inode.__default.decode__ino ...
  [0.133 s, 2 proof obligations]  verified

Verifying Impl$$_26_Inode.__default.decode__ino ...
  [0.286 s, 67 proof obligations]  verified
    """.split(
        "\n"
    )
    df = parse_df(lines)
    assert df.shape == (4, 5)
    assert df.at[3, "name"] == "__default.decode__ino"
    assert df.at[1, "time_s"] == 0.360
    assert df.at[2, "obligations"] == 2


def test_df_parse_errors():
    lines = r"""
Verifying CheckWellformed$$IndFs.IndFilesys.write ...
  [0.253 s, 5 proof obligations]  verified

Verifying Impl$$IndFs.IndFilesys.write ...
  [9.172 s, 114 proof obligations]  error
/Users/tchajed/code/daisy-nfsd/src/Dafny/examples/fs/indirect_fs.dfy(379,10): Error: A postcondition might not hold on this return path.
/Users/tchajed/code/daisy-nfsd/src/Dafny/examples/fs/indirect_fs.dfy(360,14): Related location: This is the postcondition that might not hold.
/Users/tchajed/code/daisy-nfsd/src/Dafny/examples/fs/indirect_fs.dfy(339,9): Related location
/Users/tchajed/code/daisy-nfsd/src/Dafny/examples/fs/indirect_fs.dfy(330,9): Related location
/Users/tchajed/code/daisy-nfsd/src/Dafny/examples/fs/indirect_fs.dfy(289,10): Related location
/Users/tchajed/code/daisy-nfsd/src/Dafny/examples/fs/indirect_fs.dfy(290,68): Related location
Execution trace:
    (0,0): anon0
    (0,0): anon10_Then
    (0,0): anon11_Then
    (0,0): anon12_Else

Verifying CheckWellformed$$IndFs.__default.config ...
  [0.315 s, 15 proof obligations]  verified

Verifying CheckWellformed$$IndFs.__default.config__properties ...
  [0.259 s, 1 proof obligation]  verified

Verifying Impl$$IndFs.__default.config__properties ...
  [1.582 s, 3 proof obligations]  verified

Verifying Impl$$IndFs.__default.config__totals ...
  [2.290 s, 15 proof obligations]  verified

Verifying CheckWellformed$$IndFs.__default.MkRole ...
  [0.320 s, 2 proof obligations]  verified
    """.split(
        "\n"
    )
    df = parse_df(lines)
    assert df.shape == (7, 5)
    assert df.at[1, "result"] == "error"
