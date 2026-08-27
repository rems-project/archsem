# This Makefile is provided for people that prefer to type
# "make" instead of "dune build"
.PHONY : all test clean doc doc-site serve-doc-site archive headers
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
	rm -rf _site


doc:
	dune build @doc

doc-site: doc
	./etc/mk-doc-site.sh _site

DOC_SITE_PORT ?= 8000
serve-doc-site: doc-site
	@echo "Serving documentation on http://localhost:$(DOC_SITE_PORT)/ (Ctrl-C to stop)"
	@python3 -m http.server $(DOC_SITE_PORT) -b 127.0.0.1 --directory _site


DIRS=Common
DIRS+=ArchSem
DIRS+=ArchSemArm
DIRS+=ArchSemRiscV
DIRS+=ArchSemX86
DIRS+=Extraction
DIRS+=cli

TARFILES=$(DIRS)
TARFILES+=dune-project Makefile LICENSE
TARFILES+=$(wildcard *.md)
TARFILES+=$(wildcard *.opam)
TARFILES+=$(wildcard *.opam.template)

$(TARBALL): $(TARFILES)
	$(GIT_ARCHIVE) -o $@ --prefix=$(PREFIX)/ HEAD $^

archive: $(TARBALL)

BSD2-SRC=$(shell find $(DIRS) -name '*.v' -o -name '*.ml' -o -name '*.mli' -o -name '*.mll' -o -name '*.mly')

headers:
	headache -c etc/head_config -h etc/header ${BSD2-SRC}
