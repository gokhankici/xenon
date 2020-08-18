#!/usr/bin/env python3

from collections import namedtuple
from pathlib import Path
import subprocess
import timeit
import argparse

ap = argparse.ArgumentParser()
ap.add_argument("--run-count", type=int, default=10, required=False)
args = ap.parse_args()

RUN_COUNT = args.run_count

ROOT_DIR      = Path(__file__).resolve().parent.parent
BENCHMARK_DIR = ROOT_DIR / "benchmarks"

BENCHMARK_FILES = {
  "MIPS"     : BENCHMARK_DIR / "472-mips-pipelined" / "mips_pipeline.v",
  "YARVI"    : BENCHMARK_DIR / "yarvi" / "shared" / "yarvi.v",
  "SHA256"   : BENCHMARK_DIR / "crypto_cores" / "sha_core" / "trunk" / "rtl" / "sha256.v",
  "FPU"      : BENCHMARK_DIR / "fpu" / "verilog" / "fpu.v",
  "ALU"      : BENCHMARK_DIR / "xcrypto-ref" / "rtl" / "coprocessor" / "scarv_cop_palu.v",
  "FPU2"     : BENCHMARK_DIR / "fpu2" / "divider" / "divider.v",
  "RSA"      : BENCHMARK_DIR / "crypto_cores" / "RSA4096" / "ModExp2" / "ModExp.v",
  # "AES"      : BENCHMARK_DIR / "crypto_cores" / "tiny_aes" / "trunk" / "rtl" / "aes_256.v",
  # "SCARV"    : BENCHMARK_DIR / "scarv-cpu" / "rtl" / "core" / "frv_core.v"
}

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

for b in BENCHMARKS:
    cmd = ["iodine", "--no-save", "--benchmark-mode"]
    cmd += [str(b.verilog_file), str(b.annotation_file)]
    def run():
        r = subprocess.run(cmd, cwd=ROOT_DIR, stdout=subprocess.DEVNULL)
        assert(is_ct(b) ^ r.returncode != 0)
    if RUN_COUNT > 0:
        rt = timeit.timeit(run, number=RUN_COUNT) / RUN_COUNT
        print(f"{b.name:<10}: {rt:.2f}")
    else:
        print(b.verilog_file)
