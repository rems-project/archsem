## Building

### Opam

All dependencies install instruction assume you can use `opam`. If needed,
instructions are available here: https://opam.ocaml.org/doc/Install.html.

`opam < 2.4` has a bug that might make those instructions not work, in which
case you'll need to install dependencies by hand following the lock files.

You need to add the Rocq opam repository for some of the dependencies:
```
opam repo add rocq-released --set-default https://rocq-prover.org/opam/released
```


### Lock files dependencies

We would recommend creating a new empty switch for archsem, unless you try to
integrate it somewhere else. We would recommend starting from the lock file and
then changing the dependencies you need to be different incrementally, only the
lock file dependencies are checked to work.

```
opam switch create --empty archsem-switch
```

You can then install the dependencies as specified in the lock file with:

```
opam install . --deps-only --locked --with-test
```

You can add `--with-dev-setup` if you want developement tools e.g. ocamlformat,
and `--with-doc` for documentation.

### Building

`dune build`: This build all the Rocq code and also build a fake ocaml library just to smoke test that the extraction is working.

`dune runtests`: To run tests on sequential and promising models we have.
Axiomatic model do not run (yet). Also runs ocaml unit test and CLI tests.

The `Makefile`: just calls dune directly.

## Installing with opam

Call `opam pin .` This should make the library available as 5 top-level modules for any other
projects or Rocq files.
 - ASCommon (Common infrastructure and definition)
 - ArchSem (Architecture generic part)
 - ArchSemArm (Arm instantiation)
 - ArchSemRiscV (RISC-V instantiation)
 - ArchSemX86 (x86 instantiation)

In addition it should add an `ArchSem` Ocaml library and the `archsem` CLI tool to your PATH.
