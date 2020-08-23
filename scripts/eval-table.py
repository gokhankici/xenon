#!/usr/bin/env python3

import argparse
from collections import namedtuple
from pathlib import Path
import subprocess
import statistics
import sys
from timeit import default_timer as timer

ROOT_DIR      = Path(__file__).resolve().parent.parent
BENCHMARK_DIR = ROOT_DIR / "benchmarks"

ALL_BENCHMARK_FILES = {
  "MIPS"     : BENCHMARK_DIR / "472-mips-pipelined" / "mips_pipeline.v",
  "YARVI"    : BENCHMARK_DIR / "yarvi" / "shared" / "yarvi.v",
  "SHA256"   : BENCHMARK_DIR / "crypto_cores" / "sha_core" / "trunk" / "rtl" / "sha256.v",
  "FPU"      : BENCHMARK_DIR / "fpu" / "verilog" / "fpu.v",
  "ALU"      : BENCHMARK_DIR / "xcrypto-ref" / "rtl" / "coprocessor" / "scarv_cop_palu.v",
  "FPU2"     : BENCHMARK_DIR / "fpu2" / "divider" / "divider.v",
  "RSA"      : BENCHMARK_DIR / "crypto_cores" / "RSA4096" / "ModExp2" / "ModExp.v",
  "AES"      : BENCHMARK_DIR / "crypto_cores" / "tiny_aes" / "trunk" / "rtl" / "aes_256.v",
  "SCARV"    : BENCHMARK_DIR / "scarv-cpu" / "rtl" / "core" / "frv_core.v"
}

def parse_args():
    ap = argparse.ArgumentParser(description="Runs the bencharks N times and reports the statistics about the runtimes.")
    ap.add_argument("-n", "--run-count", type=int, default=10, required=False, help="Total # runs", metavar="N")
    ap.add_argument("-i", "--ignore", action='append', default=[], required=False, help="Benchmark to ignore", metavar="NAME")
    args = ap.parse_args()

    def keep_benchmark(name):
        return not any([n.lower() in name.lower() for n in args.ignore])

    assert(args.run_count >= 2)

    bs = {n : f for n, f in ALL_BENCHMARK_FILES.items() if keep_benchmark(n) }

    return (args.run_count, bs)

RUN_COUNT, BENCHMARK_FILES = parse_args()

def is_ct(b):
    return b.name not in ["FPU2", "RSA"]

class Benchmark:
    def __init__(self, *args, **kwargs):
        if len(args) == 0:
            assert("name" in kwargs)
            assert("verilog_file" in kwargs)
            n  = kwargs.get("name")
            vf = kwargs.get("verilog_file")
            af = kwargs.get("annotation_file", self.generic_annotation_file(vf))
        elif len(args) == 2:
            n  = args[0]
            vf = args[1]
            af = self.generic_annotation_file(vf)
        elif len(args) == 3:
            n  = args[0]
            vf = args[1]
            af = args[2]
        else:
            assert(False)
        self.name            = n
        self.verilog_file    = vf
        self.annotation_file = af

    def generic_annotation_file(self, vf):
        return vf.parent / ("annot-" + vf.stem + ".json")

    def __str__(self):
        return f"{self.name}"

    def __repr__(self):
        return str(self)


BENCHMARKS = [ Benchmark(n, f) for n, f in BENCHMARK_FILES.items() ]

def run_benchmark(b, run_count):
    runs = []
    xenon = ROOT_DIR / "xenon"
    for _ in range(run_count):
        cmd = [xenon, "--no-save", "--benchmark-mode"]
        cmd += [str(b.verilog_file), str(b.annotation_file)]

        start_time = timer()
        r = subprocess.run(cmd, cwd=ROOT_DIR, stdout=subprocess.DEVNULL)
        elapsed_time = timer() - start_time

        assert(is_ct(b) ^ r.returncode != 0)
        runs.append(elapsed_time)
    return runs

stats = [ ("mean", statistics.mean)
        , ("geomean", statistics.geometric_mean)
        , ("median", statistics.median)
        , ("stdev", statistics.stdev)
        ]

def compute_stats(runs):
    res = ""
    for _, f in stats:
        s = f(runs)
        res += f"{s:>12.2f} "
    return res.rstrip()

name_header = "benchmark"
header = f"{name_header:<15} "
for s, _ in stats:
    header += f"{s:>12} "
print(header.strip())

for b in BENCHMARKS:
    if RUN_COUNT > 0:
        runs = run_benchmark(b, RUN_COUNT)
        print(f"{b.name:<15} {compute_stats(runs)}")
    else:
        print(b.verilog_file)
