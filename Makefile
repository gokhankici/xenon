all: build

build:
	cabal v2-build

test:
	./t

clean:
	cabal v2-clean

parser:
	make -C iverilog-parser

.PHONY: all build test clean parser
