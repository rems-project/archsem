# This Makefile is a bit pointless but is provided for people that prefer to type
# "make" instead of "dune build"
.PHONY : all clean
all:
	dune build

clean:
	dune clean
