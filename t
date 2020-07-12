#!/usr/bin/env python3

import sys
import os
import subprocess

PACKAGE_NAME = "iodine"
O0 = True
USE_STACK = False

def add_quotes(s):
    i = s.find(" ")
    if i < 0:
        return s
    else:
        return '"{}"'.format(s)

def run_tests(test_args, stack_args=[]):
    fast = ["--fast"] if O0 else []
    cmd = ["stack"] + stack_args + ["test"] + fast + [PACKAGE_NAME]

    if test_args:
        args = " ".join([add_quotes(a) for a in test_args])
        cmd += ["--test-arguments", args]

    try:
        return subprocess.run(cmd).returncode
    except KeyboardInterrupt:
        return 1

def run_tests_cabal(test_args):
    cmd = ["cabal", "v2-run", "iodine-test"]
    if test_args:
        cmd += ["--"] + test_args
    try:
        return subprocess.run(cmd).returncode
    except KeyboardInterrupt:
        return 1

if __name__ == "__main__":
    if USE_STACK:
        if os.getenv("PROFILE"):
            rc = run_tests(sys.argv[1:], stack_args=["--profile", "--work-dir", ".stack-work-profile"])
        else:
            rc = run_tests(sys.argv[1:])
    else:
        rc = run_tests_cabal(sys.argv[1:])
    sys.exit(rc)
