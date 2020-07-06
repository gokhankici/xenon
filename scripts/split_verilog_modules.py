#!/usr/bin/env python3

import argparse
from pathlib import Path
import re
import sys

modules = [""]

ap = argparse.ArgumentParser()
ap.add_argument("verilog_file", type=str)
ap.add_argument("output_folder", type=str)
args = ap.parse_args()

with open(args.verilog_file, "r") as f:
    for l in f:
        modules[-1] += l
        if "endmodule" in l:
            modules.append("")

modules = modules[:-2]

print(f"number of modules {len(modules)}")

prog = re.compile("module\s+(.*)\(")

output_folder = Path(args.output_folder)
output_folder.mkdir(exist_ok=True)

for m in modules:
    first_line = m.splitlines()[0]
    s = prog.search(first_line)
    filename = s.group(1)
    output_file = output_folder / (filename + ".v")
    with open(output_file, "w") as f:
        f.write(m)

