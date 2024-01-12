#!/usr/bin/env python3

from timing import get_name, get_time, parse_df


def test_name_parse():
    line = r"""Verifying TypedFs.TypedFilesys.FreeFiles (correctness) ..."""
    d = get_name(line)
    assert d is not None
    assert d["type"] == "correctness"
    assert d["name"] == "TypedFilesys.FreeFiles"


def test_timing_parse1():
    line = r"""[0.006 s, solver resource count: 15761, 3 proof obligations]  verified"""
    d = get_time(line)
    assert d is not None
    assert d["time_s"] == 0.006
    assert d["obligations"] == 3
    assert d["result"] == "ok"


def test_timing_parse2():
    line = r"""  [0.005 s, solver resource count: 9753, 1 proof obligation]  verified"""
    d = get_time(line)
    assert d is not None
    assert d["time_s"] == 0.005
    assert d["obligations"] == 1


def test_timing_parse3():
    line = r"""  [60.987 s, solver resource count: 132341, 161 proof obligations]  timed out"""
    d = get_time(line)
    assert d is not None
    assert d["time_s"] == 60.987
    assert d["result"] == "timeout"

def test_timing_parse_new():
    """Dafny 3.4 adds a new solver resource count to the trace"""
    line = r"""    [20.471 s, solver resource count: 32600962, 233 proof obligations]  timed out"""
    d = get_time(line)
    assert d is not None
    assert d["time_s"] == 20.471
    assert d["result"] == "timeout"


def test_df_parse():
    lines = r"""
Verifying TypedFs.TypedFilesys.zeroFreeSpace (well-formedness) ...
[TRACE] Using prover: /opt/homebrew/bin/z3
  [0.098 s, solver resource count: 329601, 2 proof obligations]  verified

Verifying TypedFs.TypedFilesys.zeroFreeSpace (correctness) ...
  [0.719 s, solver resource count: 4046295, 87 proof obligations]  errors
src/fs/typed_fs.dfy(597,4): Error: a postcondition could not be proved on this return path
src/fs/typed_fs.dfy(594,31): Related location: this is the postcondition that could not be proved
src/fs/typed_fs.dfy(94,9): Related location
src/fs/typed_fs.dfy(599,28): Error: a precondition for this call could not be proved
src/fs/byte_fs.dfy(1063,15): Related location: this is the precondition that could not be proved
src/fs/byte_fs.dfy(134,12): Related location

Verifying TypedFs.TypedFilesys.TotalFiles (correctness) ...
  [0.005 s, solver resource count: 9753, 1 proof obligation]  verified

Verifying TypedFs.TypedFilesys.FreeFiles (correctness) ...
  [0.006 s, solver resource count: 15761, 3 proof obligations]  verified

Dafny program verifier finished with 51 verified, 28 errors
    """.split(
        "\n"
    )
    df = parse_df(lines)
    assert df.shape == (4, 5)
    assert df.at[3, "name"] == "TypedFilesys.FreeFiles"
    assert df.at[1, "time_s"] == 0.719
    assert df.at[2, "obligations"] == 1


#def test_df_parse_errors():
#    lines = r"""
#Verifying CheckWellformed$$IndFs.IndFilesys.write ...
#  [0.253 s, 5 proof obligations]  verified
#
#Verifying Impl$$IndFs.IndFilesys.write ...
#  [9.172 s, 114 proof obligations]  error
#/Users/tchajed/code/daisy-nfsd/src/Dafny/examples/fs/indirect_fs.dfy(379,10): Error: A postcondition might not hold on this return path.
#/Users/tchajed/code/daisy-nfsd/src/Dafny/examples/fs/indirect_fs.dfy(360,14): Related location: This is the postcondition that might not hold.
#/Users/tchajed/code/daisy-nfsd/src/Dafny/examples/fs/indirect_fs.dfy(339,9): Related location
#/Users/tchajed/code/daisy-nfsd/src/Dafny/examples/fs/indirect_fs.dfy(330,9): Related location
#/Users/tchajed/code/daisy-nfsd/src/Dafny/examples/fs/indirect_fs.dfy(289,10): Related location
#/Users/tchajed/code/daisy-nfsd/src/Dafny/examples/fs/indirect_fs.dfy(290,68): Related location
#Execution trace:
#    (0,0): anon0
#    (0,0): anon10_Then
#    (0,0): anon11_Then
#    (0,0): anon12_Else
#
#Verifying CheckWellformed$$IndFs.__default.config ...
#  [0.315 s, 15 proof obligations]  verified
#
#Verifying CheckWellformed$$IndFs.__default.config__properties ...
#  [0.259 s, 1 proof obligation]  verified
#
#Verifying Impl$$IndFs.__default.config__properties ...
#  [1.582 s, 3 proof obligations]  verified
#
#Verifying Impl$$IndFs.__default.config__totals ...
#  [2.290 s, 15 proof obligations]  verified
#
#Verifying CheckWellformed$$IndFs.__default.MkRole ...
#  [0.320 s, 2 proof obligations]  verified
#    """.split(
#        "\n"
#    )
#    df = parse_df(lines)
#    assert df.shape == (7, 5)
#    assert df.at[1, "result"] == "error"
