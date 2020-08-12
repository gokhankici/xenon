DOT_FILES = $(wildcard *.dot)
PDF_FILES = $(patsubst %.dot,%.pdf,$(DOT_FILES))

all: build

build:
	cabal v2-build

test:
	./t

clean:
	cabal v2-clean

graphs: $(PDF_FILES)

$(PDF_FILES): %.pdf: %.dot
	dot -Tpdf -Gmargin=0 $< -o $@

.PHONY: all build test clean graphs
