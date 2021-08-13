#!/bin/bash

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
cd "$DIR"

./eval.py -i data bench
./eval.py -i data scale
./bench.plot -i data -o data
./scale.plot -i data -o data
