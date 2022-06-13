# ISA semantics in Coq

This folder is intended to contain all definitions needed to define the semantics
of an Instruction Set Architecture (ISA) in Coq

## Dependencies

### Bitvectors

This development use the `coq-bitvector` development at
https://gitlab.mpi-sws.org/iris/bitvector. This can be installed by doing:

```
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin --kind version coq-bitvector "dev.2022-02-27.0.37b640c2"
```
