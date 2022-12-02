## Building

(1) Install the dependencies below.

(2) Call `dune build`. This does not extract any code yet, but merely checks that the proofs pass.

The `Makefile` just calls dune directly.

## Installing with opam

(1) Install the dependencies below.

(2) Call `opam pin .` This should make the library available as 4 top-level modules for any other 
projects or coq file (assuming you are using a Coq setup from opam):
 - SSCCommon (this project extra standard library, basically a stdpp extension)
 - ISASem (The ISA Model interface)
 - GenModels (Generic model definitions)
 - PromisingArm (The promising Arm model)


## Software Dependencies

### Opam and ocaml

All dependencies install instruction assume you can use `opam`. If needed,
instructions are available here: https://opam.ocaml.org/doc/Install.html.

You need to add the coq opam repository for some of the dependencies:
```
opam repo add coq-released https://coq.inria.fr/opam/released
```


### Dune

This project uses the dune build system. It can be installed with:
```
opam install dune
```


### Coq

This project was tested with Coq 8.14. If you want exactly that version do:
```
opam pin coq 8.14.0
```
otherwise you can install it with `opam install coq`


### Sail

(1) This project uses the head version of Sail that hasn't been released yet. The
simplest to get it to clone it somewhere
```
git clone https://github.com/rems-project/sail
```

Then, if you want the precise version of sail this project was tested
against, do:
```
git checkout f421b04d
```

Then you can install sail with `opam pin .` in the `sail` directory.

(2) You will also need to install the `coq-sail` library, from the `sail` directory do:
```
opam pin lib/coq
```
This will also automatically install `coq-bbv` which is
need by the exported sail code.


### Coq libraries

For coq-hammer-tactics and coq-record-update below

#### stdpp

This development use the unstable version of `stdpp`, it can be installed by
checking out the repository:
```
git clone https://gitlab.mpi-sws.org/iris/stdpp
```

Then, if you want the precise version of stdpp this project was tested
against, do:
```
git checkout 2c03aca
```

Then you can install stdpp with `opam pin .` in the `stdpp` directory. Opam will
also propose to install `coq-stdpp-unstable` which you should accept

#### Coq Hammer

This repository uses the `sauto` family of tactics from the Coq Hammer project.
To install it, do:
```
opam install coq-hammer-tactics
```

#### Coq Record Update

This repository use the Coq record update library. To install it do:
```
opam install coq-record-update
```
