(lang dune 3.14)
(name coq-archsem)
(using coq 0.8)
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
 (name coq-archsem-common)
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
 (name coq-archsem)
 (synopsis "Coq infrastructure to reason about hardware CPU architecture semantics, architecture generic part")
 (depends
   coq-archsem-common
  (rocq-sail-stdpp (= 0.20.3)) ; See coq-archsem.opam.locked for the commit number
 )
)

(package
 (name coq-archsem-arm)
 (synopsis "Coq infrastructure to reason about hardware CPU architecture semantics, Arm instantiation")
 (depends
   coq-archsem
   (rocq-sail-tiny-arm :dev) ; See coq-archsem-arm.opam.locked for the commit number
 )
)

(package
 (name coq-archsem-riscv)
 (synopsis "Coq infrastructure to reason about hardware CPU architecture semantics, RISC-V instantiation")
 (depends
   coq-archsem
   (rocq-sail-riscv (= 0.14.1)) ; See coq-archsem-riscv.opam.locked for the commit number
 )
)

(package
 (name coq-archsem-x86)
 (synopsis "Coq infrastructure to reason about hardware CPU architecture semantics, x86 instantiation")
 (depends
   coq-archsem
   (rocq-sail-tiny-x86 :dev) ; See coq-archsem-x86.opam.locked for the commit number
 )
)

(package
 (name archsem)
 (synopsis "Archsem CLI and OCaml library to run ArchSem models")
 (depends
   coq-archsem
   coq-archsem-arm
  (otoml (>= 1.0))
  (cmdliner (>= 2.0))
  (menhir (>= 20231231))
  (ounit2 (and :with-test (>= 2.2)))
  (ocamlformat (and :with-dev-setup (>= 0.28)))
  (headache :with-dev-setup)
 )
)

(generate_opam_files)
