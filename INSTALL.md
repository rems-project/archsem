## Building

(1) Install the dependencies with `opam install . --deps-only`, See below for installing opam

(2) Call `dune build`. This does not extract any code yet, but merely checks that the proofs pass.

The `Makefile` just calls dune directly.

## Installing with opam

Call `opam pin .` This should make the library available as 4 top-level modules for any other
projects or Rocq files (assuming you are using a Rocq setup from opam):
 - ASCommon (Common infrastructure and definition)
 - ArchSem (Architecture generic part)
 - ArchSemArm (Arm instantiation)
 - ArchSemRiscV (RISC-V instantiation)


## Manual handling of dependencies

### Opam and ocaml

All dependencies install instruction assume you can use `opam`. If needed,
instructions are available here: https://opam.ocaml.org/doc/Install.html.

You need to add the Rocq opam repository for some of the dependencies:
```
opam repo add rocq-released https://rocq-prover.org/opam/released
```


### Dune

This project uses the dune build system. It can be installed with:
```
opam install dune
```


### Rocq

This project was tested with Rocq 8.19.2. If you want exactly that version do:
```
opam pin coq 8.19.2
```
otherwise you can install it with `opam install coq`

Due to Ltac2 version we don't think it will work with lower version of Rocq such
as 8.18* and below. However modifications needed are probably minimal if you do
need it.

It has been reported that it doesn't build on Rocq 8.20 yet due to some
Equations changes.

### Sail

This project uses the version 0.19 of Sail. Pin with:

```
opam pin sail 0.19
```

### Coq libraries

#### Regular coq libraries

Install via opam:

```
opam install coq-hammer-tactics coq-record-update coq-equations
```

#### stdpp

This development uses `stdpp` and `stdpp-bitvector`. They can be installed by

```
opam pin coq-stdpp 1.11.0
opam pin coq-stdpp-bitvector 1.11.0
```

#### Coq Sail (stdpp version)

The Coq Sail library is now in its own repository, to get the tested version
(just after 0.19), do the following command with the commit number in
`coq-archsem.opam.template`:

```
opam pin coq-sail-stdpp git+https://github.com/rems-project/coq-sail.git#<commit number here>
```

#### Sail Tiny Arm (for the Arm instance)

To install it, do the following command with the commit number in
`coq-archsem-arm.opam.template`:

```
opam pin coq-sail-tiny-arm git+https://github.com/rems-project/sail-tiny-arm.git#<commit number here>
```




