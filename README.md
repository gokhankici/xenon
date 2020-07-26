# Iodine

## Installation

### Dependencies

- [ghcup](https://www.haskell.org/ghcup/)
- [z3 v4.8.1](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.1)
- Ghostscript
- Graphviz

Install `ghcup` (GHC version 8.8.3) and run `cabal v2-build`.

<!--
### Dependencies (old)

- [stack](https://docs.haskellstack.org/en/stable/README/#how-to-install)
- [z3 v4.8.1](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.1)
-->

### Building

```sh
git clone --recursive https://github.com/gokhankici/iodine.git
cd iodine
make -C iverilog-parser
cabal v2-build
```

## Usage

When installed, just run `./iodine`. For the test suite, run `./t`.

### Command Line Options

```
iodine v2.0, (C) Rami Gokhan Kici 2020

Verifies whether the given Verilog file runs in constant time under the given
assumptions.

First positional argument is the verilog file to analyze.
Second positional argument is the JSON file that contains the annotations.

iodine [OPTIONS] VERILOG-FILE ANNOTATION-FILE

     --iverilog-dir=DIR  path of the iverilog-parser directory
     --print-ir          just run the verilog parser
     --vcgen             just generate the .fq file
     --no-save           do not save the fq file
     --no-fp-output      disable the output from fixpoint
     --abduction         run abduction algorithm
     --benchmark-mode    do not run the sanity check step (for benchmarking)
     --delta             run fixpoint in delta debugging mode
     --pretty-prolog     pretty print the IR generated by the Verilog file
                         before parsing
  -v --verbose           Loud verbosity
  -q --quiet             Quiet verbosity

--------------------------------------------------------------------------------
Extra arguments:
usage: iodine [-b] [--profile] [--debug] [--help]

optional arguments:
  -b, --build  Build the project
  --profile    Run in profiling mode
  --debug      Run the debugging script
  --help, -h
```

### Example

```sh
./iodine -- examples/verilog/stall.v examples/verilog/annot-stall.json
```
