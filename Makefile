# This Makefile is provided for people that prefer to type
# "make" instead of "dune build"
.PHONY : all clean doc archive headers
all:
	dune build

TARBALL=ArchSem.tar.gz
PREFIX=AS
GIT_ARCHIVE=git archive

clean:
	dune clean
	rm -f $(TARBALL)

doc:
	dune build @doc

DIRS=Common
DIRS+=ISASem
DIRS+=GenModels
DIRS+=AxiomaticModels
DIRS+=promising-arm

TARFILES=$(DIRS)
TARFILES+=dune-project Makefile LICENSE
TARFILES+=$(wildcard *.md)
TARFILES+=$(wildcard *.opam)

$(TARBALL): $(TARFILES)
	$(GIT_ARCHIVE) -o $@ --prefix=$(PREFIX)/ HEAD $^

archive: $(TARBALL)

BSD2-SRC=$(foreach dir, $(DIRS), $(wildcard $(dir)/*.v))
BSD2-SRC:=$(filter-out %/SailArmInstTypes.v, $(BSD2-SRC))

headers:
	headache -c etc/head_config -h etc/header ${BSD2-SRC}
