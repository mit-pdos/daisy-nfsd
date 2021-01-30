#!/usr/bin/env python3

from timing import get_name, get_time, parse_df


def test_name_parse():
    line = r"""Verifying CheckWellformed$$_26_Inode.__default.blks__unique ..."""
    d = get_name(line)
    assert d is not None
    assert d["type"] == "CheckWellformed"
    assert d["name"] == "__default.blks__unique"


def test_timing_parse():
    line = r"""  [0.409 s, 1 proof obligation]  verified"""
    d = get_time(line)
    assert d is not None
    assert d["time_s"] == 0.409


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
    assert df.shape == (4, 3)
    assert df.at[3, "name"] == "__default.decode__ino"
    assert df.at[1, "time_s"] == 0.360
