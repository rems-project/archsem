(lang dune 3.23)
(name rocq-archsem)
(using rocq 0.13)
(using menhir 2.1)

(source (github rems-project/archsem))
(license "BSD-2-Clause")
(authors
  "Thibaut Pérami"
  "Yeji Han"
  "Zonguyan Liu"
  "Nils Lauermann"
  "Jean Pichon-Pharabod"
  "Brian Campbell"
  "Alasdair Armstrong"
  "Ben Simner"
  "Peter Sewell"
)
(maintainers "Thibaut Pérami <thibaut.perami@cl.cam.ac.uk>")

(package
 (name rocq-archsem-common)
 (synopsis "Common infrastructure and definition for the ArchSem project, includes CDestruct and a free monad library")
 (depends
  (rocq-core (>= 9.1))
   rocq-stdlib
  (rocq-equations (>= 1.3.1))
  (coq-record-update (>= 0.3.4))
  (coq-hammer-tactics (>= 1.3.2))
  (rocq-stdpp (= 1.13.0))
  (rocq-stdpp-bitvector (= 1.13.0))
  (headache :with-dev-setup)
 )
)

(package
 (name rocq-archsem)
 (synopsis "Rocq infrastructure to reason about hardware CPU architecture semantics, architecture generic part")
 (depends
   rocq-archsem-common
  (rocq-sail-stdpp (= 0.20.3)) ; See rocq-archsem.opam.locked for the commit number
 )
)

(package
 (name rocq-archsem-arm)
 (synopsis "Rocq infrastructure to reason about hardware CPU architecture semantics, Arm instantiation")
 (depends
   rocq-archsem
   (rocq-sail-tiny-arm :dev) ; See rocq-archsem-arm.opam.locked for the commit number
 )
)

(package
 (name rocq-archsem-riscv)
 (synopsis "Rocq infrastructure to reason about hardware CPU architecture semantics, RISC-V instantiation")
 (depends
   rocq-archsem
   (rocq-sail-riscv (= 0.14.1)) ; See rocq-archsem-riscv.opam.locked for the commit number
 )
)

(package
 (name rocq-archsem-x86)
 (synopsis "Rocq infrastructure to reason about hardware CPU architecture semantics, x86 instantiation")
 (depends
   rocq-archsem
   (rocq-sail-tiny-x86 :dev) ; See rocq-archsem-x86.opam.locked for the commit number
 )
)

(package
 (name archsem)
 (synopsis "Archsem CLI and OCaml library to run ArchSem models")
 (depends
   rocq-archsem
   rocq-archsem-arm
  (otoml (>= 1.0))
  (cmdliner (>= 2.0))
  (menhir (>= 20231231))
  (ounit2 (and :with-test (>= 2.2)))
  (ocamlformat (and :with-dev-setup (>= 0.28)))
  (headache :with-dev-setup)
 )
)

(generate_opam_files)
