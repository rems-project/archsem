# This Makefile is provided for people that prefer to type
# "make" instead of "dune build"
.PHONY : all clean doc archive
all:
	dune build

TARBALL=SSC.tar.gz

clean:
	dune clean
	rm -f $(TARBALL)

doc:
	dune build @doc



TARFILES=dune-project Makefile LICENSE
TARFILES+=$(wildcard ./*.md)
TARFILES+=$(wildcard ./*.opam)
TARFILES+=$(wildcard armv9-instantiation-types/*)
TARFILES+=$(wildcard Common/*)
TARFILES+=$(wildcard ISASem/*)
TARFILES+=$(wildcard GenModels/*)
TARFILES+=$(wildcard AxiomaticModels/*)
TARFILES+=$(wildcard promising-arm/*)

$(TARBALL): $(TARFILES)
	tar -czf $(TARBALL) $(TARFILES)

archive: $(TARBALL)
