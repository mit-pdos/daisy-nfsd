#!/usr/bin/env python3

import json
import argparse
import numpy as np
import pandas as pd
import os

def read_observations(d):
    records = []
    for patchd in os.listdir(d):
        fullpatchd = os.path.join(d, patchd)
        if not os.path.isdir(fullpatchd):
            continue
        input_path = os.path.join(fullpatchd, "txnbench.json")
        with open(input_path, "rb") as f:
            for line in f:
                o = json.loads(line)
                r = {"val": o["values"]["val"]}
                r.update(o["config"])
                records.append(r)
    return pd.DataFrame.from_records(records)

def get_patch_name(fname):
    return os.path.splitext(os.path.basename(fname))[0]

def patch_cmd(df, args):
    if args.debug:
        df = df.pivot_table(
            index="bench.jrnlpatch",
            columns="bench.name",
            values="val",
            # aggfunc=[np.mean, cov_percent],
            aggfunc=[np.mean],
        )
        df = df.reorder_levels([1, 0], axis="columns")
    else:
        df = df.pivot_table(
            index="bench.name",
            columns="bench.jrnlpatch",
            values="val",
            aggfunc=np.mean,
        )
    df.index.rename("bench", inplace=True)
    if args.debug:
        print(df)
        return
    df = df.rename(get_patch_name, axis='columns')
    df.insert(0, 'orig', df.pop('orig'))
    columns = df.columns
    df.to_csv(
        os.path.join(args.output, "txn-bench.data"),
        sep="\t",
        columns=columns,
    )

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "-o",
        "--output",
        default=None,
        help="directory to output *.data file to (defaults to input dir)",
    )
    parser.add_argument(
        "-i",
        "--input",
        default=None,
        help="directory or file for input",
    )
    parser.add_argument(
        "-v",
        "--debug",
        action="store_true",
        help="print dataframes for manual inspection",
    )

    args = parser.parse_args()
    args.output = args.input

    df = read_observations(os.path.join(args.input, "patch"))
    patch_cmd(df, args)

if __name__ == "__main__":
    main()
