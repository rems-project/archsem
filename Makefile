# This Makefile is a bit pointless but is provided for people that prefer to type
# "make" instead of "dune build"
.PHONY : all clean
all:
	dune build

clean:
	dune clean
	rm -f ssc.tar.gz

archive:
	tar -czf ssc.tar.gz dune dune-project INSTALL.md README.md Makefile coq-system-semantics.opam LICENSE Common ISASem armv9-instantiation-types GenModels promising-arm
