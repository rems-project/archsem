#!/bin/sh
#                               ArchSem
#
# Copyright (c) 2021
#     Thibaut Pérami, University of Cambridge
#     Yeji Han, Seoul National University
#     Shreeka Lohani, University of Cambridge
#     Zongyuan Liu, Aarhus University
#     Nils Lauermann, University of Cambridge
#     Jean Pichon-Pharabod, University of Cambridge, Aarhus University
#     Brian Campbell, University of Edinburgh
#     Alasdair Armstrong, University of Cambridge
#     Ben Simner, University of Cambridge
#     Peter Sewell, University of Cambridge
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions
# are met:
#
#  1. Redistributions of source code must retain the above copyright
#     notice, this list of conditions and the following disclaimer.
#
#  2. Redistributions in binary form must reproduce the above copyright
#     notice, this list of conditions and the following disclaimer in the
#     documentation and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
# FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
# COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
# INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
# BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS
# OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
# ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
# TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
# USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

# Assemble the coqdoc and odoc output produced by `dune build @doc` into a
# single self-contained website, ready to be served by GitHub Pages.
#
# Usage: etc/mk-doc-site.sh [output-dir]   (run from the repository root)

set -eu

out=${1:-_site}

build=_build/default
odoc=$build/_doc/_html

# The documented Rocq theories, as "<source dir>:<theory name>" pairs.
theories="Common:ASCommon
ArchSem:ArchSem
ArchSemArm:ArchSemArm
ArchSemRiscV:ArchSemRiscV
ArchSemX86:ArchSemX86"

die() {
  echo "mk-doc-site: $1" >&2
  echo "mk-doc-site: run 'dune build @doc' first" >&2
  exit 1
}

[ -d "$odoc" ] || die "missing $odoc"
for pair in $theories; do
  dir=${pair%:*}
  theory=${pair#*:}
  [ -d "$build/$dir/$theory.html" ] || die "missing $build/$dir/$theory.html"
done

rm -rf "$out"
mkdir -p "$out/ocaml" "$out/rocq"

# odoc output is already a complete site.
cp -r "$odoc/." "$out/ocaml/"

# coqdoc cross-theory links are currently relative to the build tree via the
# `--external` flags in dune file. The simplest way to make this work also for
# the published site is to respect the layout
for pair in $theories; do
  dir=${pair%:*}
  theory=${pair#*:}
  mkdir -p "$out/rocq/$dir"
  cp -r "$build/$dir/$theory.html" "$out/rocq/$dir/"
done

cp etc/doc-index.html "$out/index.html"
cp etc/logo/archsem_logo4.png "$out/archsem_logo.png"

# dune leaves its build artifacts read-only; the copies inherit that, which
# makes the result awkward to clean up or tweak by hand.
chmod -R u+w "$out"
