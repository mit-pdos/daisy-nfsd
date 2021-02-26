#!/usr/bin/python

import sys
import os
import os.path

(_, dstdir) = sys.argv

for (dir, _, files) in os.walk("."):
    os.mkdir(os.path.abspath(os.path.join(dstdir, dir)))
    for fn in files:
        with open(os.path.join(dir, fn)) as src:
            with open(os.path.join(dstdir, dir, fn), "w") as dst:
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
                                    imppath = (
                                        "github.com/mit-pdos/dafny-jrnl/dafnygen/"
                                        + imppath
                                    )
                                l = '%s "%s"\n' % (impname, imppath)
                    dst.write(l)
