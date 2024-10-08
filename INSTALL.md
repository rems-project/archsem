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
 - PromisingArm (The promising Arm models)


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

This project was tested with Coq 8.19.1. If you want exactly that version do:
```
opam pin coq 8.19.2
```
otherwise you can install it with `opam install coq`

Due to Ltac2 version we don't think it will work with lower version of Coq such
as 8.18* and below. However modifications needed are probably minimal if you do
need it. At the time of writing some dependencies are not ported yet to Coq 8.20
and later.


### Sail

This project temporarily doesn't use Sail for technical reason, as generated files
have been checked in, it will start using Sail again later. As reference the
previous text is here:

> This project uses the head version of Sail that hasn't been released yet. The
> simplest to get it to clone it somewhere
> ```
> git clone https://github.com/rems-project/sail
> ```
>
> Then, if you want the precise version of sail this project was tested
> against, do:
> ```
> git checkout f421b04d
> ```
>
> Then you can install sail with `opam pin .` in the `sail` directory.


### Coq libraries

#### Regular coq libraries

Install via opam
```
opam install coq-hammer-tactics coq-record-update coq-equations
```

#### stdpp

This development uses `stdpp` and its splitoff `stdpp-bitvector`, it can be installed by
checking out the repository:
```
git clone https://gitlab.mpi-sws.org/iris/stdpp
```

Then, if you want the precise version of stdpp this project was tested
against, do:
```
git checkout coq-stdpp-1.10.0
```

Then you can install stdpp with `opam pin .` in the `stdpp` directory. Opam will
also propose to install `coq-stdpp-unstable` which you should accept.


#### Coq Sail (stdpp version)

The Coq Sail library is now in its own repository, do:

```
git clone https://github.com/rems-project/coq-sail
```

Then (optionally), in that repository, if you want the version used for development, do:
```
git checkout 562597f
```

Then you can install `coq-sail-stdpp` with `opam pin coq-sail-stdpp .` in the
repository.


