#!/usr/bin/env python3

import sys
import os
import typing
from os import path


def process_file(src: typing.TextIO, dst: typing.TextIO):
    """Fix imports in file src and write output to dst."""
    imports = 0
    for l in src.readlines():
        if l.strip() == "import (":
            imports += 1
        elif imports == 1:
            if l.strip() == ")":
                imports += 1
            else:
                parts = l.strip().split()
                if len(parts) == 2:
                    impname = parts[0]
                    imppath = parts[1].replace('"', "")
                    if "/" not in imppath and imppath != "reflect":
                        imppath = "github.com/mit-pdos/daisy-nfsd/dafnygen/" + imppath
                    l = '%s "%s"\n' % (impname, imppath)
        dst.write(l)


def main():
    if len(sys.argv) != 2:
        print("Usage: dafnygen-imports.py <output-dir>", file=sys.stderr)
        sys.exit(1)
    dstdir = sys.argv[1]
    for (dirpath, _, files) in os.walk("."):
        os.mkdir(path.abspath(path.join(dstdir, dirpath)))
        for fn in files:
            with open(path.join(dirpath, fn)) as src:
                with open(path.join(dstdir, dirpath, fn), "w") as dst:
                    process_file(src, dst)


if __name__ == "__main__":
    main()
