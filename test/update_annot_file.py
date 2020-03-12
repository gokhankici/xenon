#!/usr/bin/env python3

import argparse
import json
from pathlib import Path
import subprocess
import sys

def err(msg):
    print(msg, file=sys.stderr)
    sys.exit(1)

def parse_args():
    ap = argparse.ArgumentParser(description="updates the old annotation format to the new one")
    ap.add_argument("annot_file", metavar="ANNOT-FILE", type=argparse.FileType('r'), help="Annotation file")
    ap.add_argument("--has-clock", type=str, action='append', metavar="MODULE-NAME", help="module with a clock")
    ap.add_argument("--top-module", type=str, required=True, metavar="MODULE-NAME", help="top module name")
    ap.add_argument("--replace", action="store_true", default=False, help="replace the original file")
    args = ap.parse_args()
    return args

args = parse_args()
ANNOT_FILE = Path(args.annot_file.name).resolve()
NEW_ANNOT_FILE = ANNOT_FILE.parent / (ANNOT_FILE.stem + "_fixed.json")

annots = json.load(args.annot_file)

OTHER_TYPES = set(["blocklist", "history", "qualifiers-history", "qualifiers"])
annot_diff = set(annots.keys()) - set(["clock", "annotations"]) - OTHER_TYPES
if annot_diff:
    err(f"Unknown annotations: {annot_diff}")

################################################################################
# clock ########################################################################
################################################################################

clock     = annots["clock"] if "clock" in annots else None
has_clock = set(args.has_clock) if args.has_clock is not None else set()

if has_clock and not clock:
    err("some modules have a clock but clock name is not in the file")

has_clock.add(args.top_module)

################################################################################
# creating the new format ######################################################
################################################################################

new_format = {}

new_format["top_module"] = args.top_module
new_format["modules"] = {}

def set_module_annot(module_name, annot_type, value):
    if module_name not in new_format["modules"]:
        new_format["modules"][module_name] = {"annotations": {}}
    if "annotations" not in new_format["modules"][module_name]:
        new_format["modules"][module_name]["annotations"] = {}
    new_format["modules"][module_name]["annotations"][annot_type] = value

def set_module_clock(module_name, value):
    if module_name not in new_format["modules"]:
        new_format["modules"][module_name] = {}
    new_format["modules"][module_name]["clock"] = value

def get_module_annot(module_name, annot_type):
    return new_format["modules"][module_name]["annotations"][annot_type]

def has_module_annot(module_name, annot_type):
    try:
        return annot_type in new_format["modules"][module_name]["annotations"]
    except KeyError:
        return False

for annot in annots["annotations"]:
    module_name = annot["module"] if "module" in annot else args.top_module
    annot_type = annot["type"]

    if has_module_annot(module_name, annot_type):
        err(f"{module_name} has multiple annotations of the form {annot_type}")

    set_module_annot(module_name, annot_type, annot["variables"])

for module_name in has_clock:
    set_module_clock(module_name, clock)

for t in OTHER_TYPES:
    if t in annots:
        new_format[t] = annots[t]

################################################################################
# writing the new format #######################################################
################################################################################

with open(NEW_ANNOT_FILE, "w") as f:
    json.dump(new_format, f, indent=2)

if args.replace:
    BAK_ANNOT_FILE = ANNOT_FILE.with_suffix(".json.bak")
    subprocess.run(["mv", ANNOT_FILE, BAK_ANNOT_FILE])
    subprocess.run(["mv", NEW_ANNOT_FILE, ANNOT_FILE])
