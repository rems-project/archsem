# This Makefile is provided for people that prefer to type
# "make" instead of "dune build"
.PHONY : all clean doc archive headers
all:
	dune build

test:
	dune runtest

TARBALL=ArchSem.tar.gz
PREFIX=ArchSem
GIT_ARCHIVE=git archive

clean:
	dune clean
	rm -f $(TARBALL)

doc:
	dune build @doc

DIRS=Common
DIRS+=ArchSem
DIRS+=ArchSemArm
DIRS+=ArchSemRiscV
DIRS+=ArchSemX86
DIRS+=Extraction

TARFILES=$(DIRS)
TARFILES+=dune-project Makefile LICENSE
TARFILES+=$(wildcard *.md)
TARFILES+=$(wildcard *.opam)
TARFILES+=$(wildcard *.opam.template)

$(TARBALL): $(TARFILES)
	$(GIT_ARCHIVE) -o $@ --prefix=$(PREFIX)/ HEAD $^

archive: $(TARBALL)

BSD2-SRC=$(foreach dir, $(DIRS), $(wildcard $(dir)/*.v $(dir)/tests/*.v))

headers:
	headache -c etc/head_config -h etc/header ${BSD2-SRC}
