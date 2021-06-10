#!/usr/bin/env python3

import sys
import re

import argparse
import pandas as pd


def parse_raw(lines):
    """Construct a dataframe of observations from raw output as lines."""
    fs = None
    data = []

    for line in lines:
        if re.match(r"""^#""", line):
            continue
        m = re.match(r"""fs=(?P<fs>.*)""", line)
        if m:
            fs = m.group("fs")
            continue
        m = re.match(
            r"""fs-smallfile: (?P<clients>\d*) (?P<val>[0-9.]*) file/sec""",
            line,
        )
        if m:
            data.append(
                {
                    "fs": fs,
                    "clients": int(m.group("clients")),
                    "throughput": float(m.group("val")),
                }
            )
            continue
        print("ignored line: " + line, end="", file=sys.stderr)

    return pd.DataFrame.from_records(data)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("bench", type=argparse.FileType("r"))

    args = parser.parse_args()

    tidy_df = parse_raw(args.bench)
    df = tidy_df.pivot_table(index="clients", columns="fs", values="throughput")
    with open("data/dnfs.data", "w") as f:
        print(df["dnfs"].to_csv(sep="\t", header=False), end="", file=f)
    with open("data/gnfs.data", "w") as f:
        print(df["gonfs"].to_csv(sep="\t", header=False), end="", file=f)
    with open("data/linux-nfs.data", "w") as f:
        print(df["linux"].to_csv(sep="\t", header=False), end="", file=f)
    if "serial-dnfs" in df.columns:
        with open("data/serial.data", "w") as f:
            print(df["serial-dnfs"].to_csv(sep="\t", header=False), end="", file=f)
