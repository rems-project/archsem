# This Makefile is provided for people that prefer to type
# "make" instead of "dune build"
.PHONY : all clean doc archive
all:
	dune build

TARBALL=SSC.tar.gz
PREFIX=SSC
GIT_ARCHIVE=git archive

clean:
	dune clean
	rm -f $(TARBALL)

doc:
	dune build @doc

TARFILES=dune-project Makefile LICENSE
TARFILES+=$(wildcard *.md)
TARFILES+=$(wildcard *.opam)
TARFILES+=armv9-instantiation-types
TARFILES+=Common
TARFILES+=ISASem
TARFILES+=GenModels
TARFILES+=AxiomaticModels
TARFILES+=promising-arm

$(TARBALL): $(TARFILES)
	$(GIT_ARCHIVE) -o $@ --prefix=$(PREFIX)/ HEAD $^

archive: $(TARBALL)
