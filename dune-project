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
 (name coq-archsem)
 (synopsis "Coq infrastructure to reason about hardware CPU architecture semantics")
 (depends
  (coq (>= 8.19.2))
   coq-stdlib
  (coq-equations (>= 1.3))
  (coq-record-update (>= 0.3.4))
  (coq-hammer-tactics (>= 1.3.2))
  (coq-stdpp (= 1.10.0))
  (coq-stdpp-bitvector (= 1.10.0))
  (coq-sail-stdpp :dev) ; See INSTALL.md for the commit number
 )
)

(generate_opam_files)
