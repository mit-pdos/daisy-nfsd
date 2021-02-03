#!/usr/bin/env python3

# process Dafny's /trace output and organizing timing info

import sys
import re
from typing import List, Dict, Any
import pandas as pd

NAME_RE = re.compile(
    r"""Verifying\s
    (?P<type>\w*)\$\$
    (?P<module>[a-zA-Z0-9_]*)\.
    (?P<name>[a-zA-Z0-9_.]*)
    \s\.\.\.
    """,
    re.VERBOSE,
)


def get_name(line):
    m = NAME_RE.match(line)
    if m is None:
        return None
    return {"type": m.group("type"), "name": m.group("name")}


TIME_RE = re.compile(
    r"""
    \s*\[
    (?P<time>[0-9.]*)
    \s s,
    \s* (?P<num_obligations>[0-9]*)\ proof\ obligations?\]
    \s*verified
    """,
    re.VERBOSE,
)


def get_time(line):
    m = TIME_RE.match(line)
    if m is None:
        return None
    return {
        "time_s": float(m.group("time")),
        "obligations": int(m.group("num_obligations")),
    }


def parse_df(lines) -> pd.DataFrame:
    current = None
    data: List[Dict[str, Any]] = []

    for line in lines:
        line = line.rstrip("\n")
        if current is None:
            current = get_name(line)
            continue

        # should find timing after a name
        timing = get_time(line)
        if timing is None:
            print(f"did not find timing info for {current}", file=sys.stderr)
            current = None
            continue
        current.update(timing)
        data.append(current)
        current = None

    df = pd.DataFrame.from_records(
        data, columns=["type", "name", "obligations", "time_s"]
    )
    if df is None:
        sys.exit(1)
        raise ValueError()
    return df
