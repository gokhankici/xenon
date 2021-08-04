# Xenon

## Installation

### Dependencies

- [GHC 8.8.4](https://www.haskell.org/ghc/download_ghc_8_8_4.html): Can be
  installed using [ghcup](https://www.haskell.org/ghcup/)
- [z3 v4.8.1](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.1)
- [GLPK (GNU Linear Programming Kit) v.4.65](https://ftp.gnu.org/gnu/glpk/glpk-4.65.tar.gz)
- Ghostscript & Graphviz (required for generating the graphs)

### Building

```sh
# 1. install ghc 8.8.4 using ghcup
open "https://www.haskell.org/ghcup/"

# 2. clone xenon
git clone --recursive https://github.com/gokhankici/xenon.git
cd xenon

# 3. build the Verilog parser
make parser

# 4. build the project
make
```

