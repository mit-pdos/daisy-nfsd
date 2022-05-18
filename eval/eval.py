#!/usr/bin/env python3

from os import path
import argparse
import gzip
import json
import numpy as np
import pandas as pd


def read_records(f):
    """Read a list of records."""
    records = []
    for line in f:
        o = json.loads(line)
        r = {"val": o["values"]["val"]}
        r.update(o["config"])
        records.append(r)
    return records


def cov_percent(data):
    return round((np.std(data) / np.mean(data)) * 100, 2)


def bench_cmd(records, args):
    df = pd.DataFrame.from_records(records)
    benches = ["smallfile", "largefile", "app"]
    if args.debug:
        df = df.pivot_table(
            index="fs.name",
            columns="bench.name",
            values="val",
            aggfunc=[np.mean, cov_percent],
        )
        df = df.reorder_levels([1, 0], axis="columns")
        df = df[benches]
    else:
        df = df.pivot_table(
            index="bench.name",
            columns="fs.name",
            values="val",
            aggfunc=np.mean,
        )
        df = df.reindex(index=benches)
    df.index.rename("bench", inplace=True)
    if args.debug:
        print(df)
        return
    columns = [
        "linux",
        "linux-ordered",
        "daisy-nfsd",
        "daisy-nfsd-seq-wal",
        "daisy-nfsd-seq-txn",
        "go-nfsd",
        "fscq",
    ]
    # filter to the columns that actually show up in the data
    columns = [x for x in columns if x in df.columns]
    df.to_csv(
        path.join(args.output, "bench.data"),
        sep="\t",
        columns=columns,
    )


def extended_bench_cmd(records, args):
    smallfile_thread_counts = set([])
    for r in records:
        if r["bench.name"] == "smallfile":
            threads = r["bench.start"]
            smallfile_thread_counts.add(threads)
            r["bench.name"] = f"smallfile-{threads}"
    df = pd.DataFrame.from_records(records)
    benches = [f"smallfile-{t}" for t in sorted(smallfile_thread_counts)] + [
        "largefile",
        "app",
    ]
    if args.debug:
        df = df.pivot_table(
            index="fs.name",
            columns="bench.name",
            values="val",
            aggfunc=[np.mean, cov_percent],
        )
        df = df.reorder_levels([1, 0], axis="columns")
        df = df[benches]
    else:
        df = df.pivot_table(
            index="bench.name",
            columns="fs.name",
            values="val",
            aggfunc=np.mean,
        )
        df = df.reindex(index=benches)
    df.index.rename("bench", inplace=True)
    if args.debug:
        print(df)
        return
    columns = [
        "linux",
        "linux-ordered",
        "daisy-nfsd",
        "daisy-nfsd-seq-txn",
        "daisy-nfsd-seq-wal",
    ]
    # filter to the columns that actually show up in the data
    columns = [x for x in columns if x in df.columns]
    df.to_csv(
        path.join(args.output, "extended-bench.data"),
        sep="\t",
        columns=columns,
    )


def scale_cmd(records, args):
    df = pd.DataFrame.from_records(records)
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
    for fs in df.columns:
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

    parser_extended = subparsers.add_parser(
        "extended-bench", help="benchmarks on several file systems"
    )
    parser_extended.set_defaults(func=extended_bench_cmd)

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
        records = read_records(f)
    args.func(records, args)


if __name__ == "__main__":
    main()
