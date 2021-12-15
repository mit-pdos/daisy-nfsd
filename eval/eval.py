#!/usr/bin/env python3

from os import path
import argparse
import gzip
import json
import numpy as np
import pandas as pd


def read_observations(f):
    """Read a tidy DataFrame."""
    records = []
    for line in f:
        o = json.loads(line)
        r = {"val": o["values"]["val"]}
        r.update(o["config"])
        records.append(r)
    return pd.DataFrame.from_records(records)


def cov_percent(data):
    return round((np.std(data) / np.mean(data)) * 100, 2)


def bench_cmd(df, args):
    if args.debug:
        df = df.pivot_table(
            index="fs.name",
            columns="bench.name",
            values="val",
            aggfunc=[np.mean, cov_percent],
        )
        df = df.reorder_levels([1, 0], axis="columns")
        df = df[["smallfile", "largefile", "app"]]
    else:
        df = df.pivot_table(
            index="bench.name",
            columns="fs.name",
            values="val",
            aggfunc=np.mean,
        )
        df = df.reindex(index=["smallfile", "largefile", "app"])
    df.index.rename("bench", inplace=True)
    if args.debug:
        print(df)
        return
    columns = ["linux", "daisy-nfsd", "go-nfsd"]
    # filter to the columns that actually show up in the data
    columns = [x for x in columns if x in df.columns]
    if "fscq" in df.columns:
        columns.append("fscq")
    df.to_csv(
        path.join(args.output, "bench.data"),
        sep="\t",
        columns=columns,
    )


def scale_cmd(df, args):

    if args.debug:
        df = df.pivot_table(
            index="bench.start",
            columns="fs.name",
            values="val",
            aggfunc=[np.mean, cov_percent],
        )
        df = df.reorder_levels([1, 0], axis="columns")
    else:
        df = df.pivot_table(
            index="bench.start",
            columns="fs.name",
            values="val",
            aggfunc=np.mean,
        )
    df.index.rename("threads", inplace=True)
    if args.debug:
        print(df)
        return
    # just for manual inspection
    df.to_csv(
        path.join(args.output, "scale.data"),
        sep="\t",
    )
    for fs in ["linux", "daisy-nfsd", "go-nfsd"]:
        if fs not in df:
            continue
        with open(path.join(args.output, f"{fs}.data"), "w") as f:
            print(df[fs].to_csv(sep="\t", header=False), end="", file=f)


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

    subparsers = parser.add_subparsers(dest="dataset_name")
    parser_bench = subparsers.add_parser(
        "bench", help="smallfile, largefile, app"
    )
    parser_bench.set_defaults(func=bench_cmd)

    parser_scale = subparsers.add_parser(
        "scale", help="smallfile scaling benchmark"
    )
    parser_scale.set_defaults(func=scale_cmd)

    args = parser.parse_args()

    # automatically use command name if a directory is provided
    if path.isdir(args.input):
        input_path = path.join(args.input, f"{args.dataset_name}.json")
        args.output = args.input
    else:
        input_path = args.input
    with open(input_path, "rb") as f:
        if input_path.endswith(".gz"):
            f = gzip.GzipFile(fileobj=f)
        df = read_observations(f)
    args.func(df, args)


if __name__ == "__main__":
    main()
