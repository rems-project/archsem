## Building

### Opam and ocaml

All dependencies install instruction assume you can use `opam`. If needed,
instructions are available here: https://opam.ocaml.org/doc/Install.html.

We use ocaml 4.14.2, so if you want to make sure to have same configuration, please create a switch with that version of ocaml.

You need to add the Rocq opam repository for some of the dependencies:
```
opam repo add rocq-released https://rocq-prover.org/opam/released
```


### Dependencies

Install the dependencies with:
```
opam pin coq 8.19.2
opam pin coq-stdpp 1.11.0
opam pin coq-stdpp-bitvector 1.11.0
opam install . --deps-only
```

You can play with different version of Rocq but right now we think neither 8.18
nor 8.20 work due to respectively Ltac2 problems and Equations problems.

### Building

`dune build` This build all the Rocq code and also build a fake ocaml library just to smoke test that the extraction is working.

`dune runtests` To run some small sequential tests.

The `Makefile` just calls dune directly.

## Installing with opam

Call `opam pin .` This should make the library available as 4 top-level modules for any other
projects or Rocq files (assuming you are using a Rocq setup from opam):
 - ASCommon (Common infrastructure and definition)
 - ArchSem (Architecture generic part)
 - ArchSemArm (Arm instantiation)
 - ArchSemRiscV (RISC-V instantiation)
