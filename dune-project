(lang dune 3.8)
(name coq-archsem)
(using coq 0.8)

(source (github rems-project/archsem))
(license "BSD-2-Clause")
(authors
  "Thibaut Pérami"
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
  (coq (>= 9.0))
   coq-stdlib
  (coq-equations (>= 1.3))
  (coq-record-update (>= 0.3.4))
  (coq-hammer-tactics (>= 1.3.2))
  (coq-stdpp (= 1.12.0))
  (coq-stdpp-bitvector (= 1.12.0))
  (otoml (= 1.0.5))
 )
)

(package
 (name coq-archsem)
 (synopsis "Coq infrastructure to reason about hardware CPU architecture semantics, architecture generic part")
 (depends
   coq-archsem-common ; need same commit
  (coq-sail-stdpp (= 0.20)) ; See coq-archsem.opam.template for the commit number
 )
)

(package
 (name coq-archsem-arm)
 (synopsis "Coq infrastructure to reason about hardware CPU architecture semantics, Arm instantiation")
 (depends
   coq-archsem
   (coq-sail-tiny-arm :dev) ; See coq-archsem-arm.opam.template for the commit number
 )
)

(package
 (name coq-archsem-riscv)
 (synopsis "Coq infrastructure to reason about hardware CPU architecture semantics, RISC-V instantiation")
 (depends
   coq-archsem
   (coq-sail-riscv :dev) ; See coq-archsem-riscv.opam.template for the commit number
 )
)

(generate_opam_files)
