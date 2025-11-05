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
opam pin coq 9.0.1
opam pin coq-stdpp 1.12.0
opam pin coq-stdpp-bitvector 1.12.0
opam install . --deps-only
```

You can try to play with different version of Rocq but it requires some futzing
with dune to go before 9.0 and some of the required packaged are not released
for 9.1 or later at the time of writing. Raise an issue if you need Rocq 8.20
support and we can make a branch

### Building

`dune build`: This build all the Rocq code and also build a fake ocaml library just to smoke test that the extraction is working.

`dune runtests`: To run tests on sequential and promising models we have.
Axiomatic model do not run (yet)

The `Makefile`: just calls dune directly.

## Installing with opam

Call `opam pin .` This should make the library available as 4 top-level modules for any other
projects or Rocq files (assuming you are using a Rocq setup from opam):
 - ASCommon (Common infrastructure and definition)
 - ArchSem (Architecture generic part)
 - ArchSemArm (Arm instantiation)
 - ArchSemRiscV (RISC-V instantiation)
