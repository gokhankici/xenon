#!/usr/bin/env python3

import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT_DIR = Path(__file__).parent.parent.resolve()

def to_abs(f):
    return Path(f).resolve()

def indent_json(filename):
    with open(filename, "r") as f:
        j = json.load(f)
    print(json.dumps(j, indent=2))
    with open(filename, "w") as f:
        json.dump(j, f, indent=2)

ap = argparse.ArgumentParser(description="Generates a skeleton annotation file")
ap.add_argument("verilog_file")
ap.add_argument("--topmodule")
ap.add_argument("--annotation-file")
ap.add_argument("--check", action='store_true', default=False)
ap.add_argument("-I", "--include-dir", action="append", type=str, default=[])

args = ap.parse_args()

vf = to_abs(args.verilog_file)

if not args.topmodule:
    args.topmodule = vf.stem

if not args.annotation_file:
    args.annotation_file = vf.parent / ('annot-' + vf.stem + '.json')

r = subprocess.run(
      ["cabal", "v2-run", "iodine-debug", "--", "generate-annotation-file",
       vf, args.topmodule, to_abs(args.annotation_file)] + args.include_dir,
      cwd=ROOT_DIR)

if r.returncode == 0:
    indent_json(args.annotation_file)

if args.check:
    subprocess.run(
        ["./iodine", to_abs(args.verilog_file), to_abs(args.annotation_file)],
        cwd=ROOT_DIR
        )
