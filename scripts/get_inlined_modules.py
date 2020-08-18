#!/usr/bin/env python3

import json
import sys

if len(sys.argv) != 2:
    print(f"usage {__file__} <annotation file>")
    sys.exit(1)

with open(sys.argv[1], "r") as f:
    j = json.load(f)

    topmodule = j["top_module"]

    cnt = 0
    for i, (modulename, annots) in enumerate(j["modules"].items()):
        inlined = annots["inline"] if "inline" in annots else False
        is_top = modulename == topmodule
        if inlined and not is_top:
            cnt += 1
        msg = " (TOP MODULE)" if is_top else ""
        print(f"{i+1:2d}. {modulename:30s} {inlined}{msg}")
    print(f"\nTotal count: {cnt}")
