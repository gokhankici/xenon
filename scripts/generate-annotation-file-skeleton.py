#!/usr/bin/env python3

import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT_DIR = Path(__file__).parent.parent.resolve()

ap = argparse.ArgumentParser(description="Generates a skeleton annotation file")
ap.add_argument("verilog_file")
ap.add_argument("topmodule")
ap.add_argument("annot_file")
ap.add_argument("--check", action='store_true', default=False)
args = ap.parse_args()

def toabs(f):
    return Path(f).resolve()

def indent_json(filename):
    with open(filename, "r") as f:
        j = json.load(f)
    with open(filename, "w") as f:
        json.dump(j, f, indent=2)

subprocess.run(
      ["cabal", "v2-run", "iodine-debug", "--", "generate-annotation-file",
       toabs(args.verilog_file), args.topmodule, toabs(args.annot_file)],
      cwd=ROOT_DIR)

indent_json(args.annot_file)

if args.check:
    subprocess.run(["./iodine", toabs(args.verilog_file), toabs(args.annot_file)], cwd=ROOT_DIR)
