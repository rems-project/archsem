![ArchSem logo](/../main/etc/logo/archsem_logo4.png?raw=true)


# ArchSem

ArchSem is a Rocq framework to define the semantics of CPU architectures
such as Arm-A, RISC-V, and x86, integrating their concurrency and instruction-set semantics.
The framework is designed to be generic, but so far is only instantiated for Arm-A, RISC-V and x86.

## Paper

[ArchSem: Reusable Rigorous Semantics of Relaxed Architectures](https://www.cl.cam.ac.uk/~pes20/Stuff/2025-archsem-paper.pdf). 
Thibaut Pérami, Thomas Bauereiss, Brian Campbell, Zongyuan Liu, Nils Lauermann, Alasdair Armstrong, and Peter Sewell.
In POPL 2026.
[doi](https://doi.org/10.1145/3776650)




## General goals and organization

In order to build an architecture model one needs two components:
- An _ISA model_ that provides the semantics of instructions. Those are intended
  to be derived from [Sail](https://github.com/rems-project/sail) or
  [ASL](https://developer.arm.com/Architectures/Architecture%20Specification%20Language)
  specifications such as [sail-arm](https://github.com/rems-project/sail-arm) (via Sail).
  Currently we only have a pipeline to import those from Sail definitions
- A _concurrency model_ that defines how the instructions interact with each
  other, both in the same thread and between threads.  In other words, a
  concurrency model is the missing part that take one from an ISA model to a
  full architecture model. It is generally much smaller but much
  more intricate than the instruction semantics. It contains both simple details like piping registers from
  one instruction to the next all the way up to user relaxed-concurrency models and 
  system-level concurrency models that have features such as instruction
  fetching, virtual memory and architectural exceptions. Those concurrency
  models will be written directly in Rocq for the immediate future, although
  we plan ways to import the relaxed memory parts from existing relaxed
  memory tools such as [Herd](https://github.com/herd/herdtools7) or
  [Isla Axiomatic](https://github.com/rems-project/isla).

ArchSem defines an [_Interface_](ArchSem/Interface.v) between the two so
that they can interoperate properly. It is based on free monads (which are finite
itrees, because the semantics of a single instruction cannot diverge). The interface is
therefore mainly defined by the set of effects an instruction can call. This is
mostly generic but allows precise architecture-specific customization points.
This interface is derived from the Sail "outcomes" used by concurrency-aware
Sail specifications. This allows one to plug an arbitrary ISA model with an arbitrary
concurrency model and obtain an architecture model. It also allows making
proofs about concurrency model against an arbitrary universally quantified ISA
model and vice versa.

More generally what want to enable with this framework includes:
- Proving properties of CPU architectures
- Proving correctness of software running on an architecture, especially system
  software, in particular with the use of higher-level program logics, often
  built using [Iris](https://iris-project.org/)
- Proving correctness of compilers or compiler passes targeting the
  architecture, including concurrency aspects
- Proving equivalences and refinements between different models
- Executing models on simple litmus tests to evaluate them and compare them to
  other executable models
- As a design tool to support thinking about architecture models for new features

This places some constraints on how the framework can work, and in particular on
the interface between ISA and concurrency models:
- Things must as executable as possible. Our interface requires ISA model to be
  executable, therefore if a concurrency model is made to be executable, the
  resulting combination is executable. However, we haven't yet finished the
  extraction pipeline and utilities to parse litmus tests to run. so we have
  only run hand written sequential tests so far.
- The interface must support all kinds of concurrency models: axiomatic,
  micro-architectural operational, promising, etc. We have not implemented any
  mirco-architectural operational model so far but we have axiomatic and
  promising model
- All models can be partial, so the framework must handle partiality properly.
  ISA models can fail at any point and those failures must be correctly
  propagated upwards. This is not fully operational for axiomatic model due to
  theory limitations about the consistency of partial model, so the current UB
  handling of axiomatic model might be unsound.

## Building

See [INSTALL.md](INSTALL.md) for dependencies, installation, and build
instructions.

## Rocq automation

There are some powerful custom tactics in `Common`, as well as useful but
generic library. See the [README](Common/README.md) there for more details. In
particular `cdestruct` is in [Common/CDestruct.v](Common/CDestruct.v).

## The current state and directory structure

- `Common` (Rocq module name `ASCommon`) is the "utils" library. It contains all
  non-ArchSem-specific Rocq lemmas and automation, as well as required theories
  such that executable relational algebra or effects and free monads.
  This includes:
  - `CDestruct.v` The implementation of the `cdestruct` tactic
- `ArchSem` The architecture generic part of the projects, this includes
  - `Interface.v` The definition of the interface between ISA models and
    concurency models
  - `CandidateExecution.v` The definition of candidate executions for weak
    memory model
- `ArchSemArm` The Armv9-A instantiation of the library. This includes;
  - A sequential operational model (`ArmSeqModel.v`)
  - A User-mode promising model (`UMPromising.v`), similar to
    [the PLDI19 paper](https://sf.snu.ac.kr/publications/promising-arm-riscv.pdf)
  - A very WIP VMSA promising model (`VMPromising.v`)
  - A User-mode axiomatic model (`UMArm.v`)
  - An SC model for Arm (`UMSeqArm.v`) that is unsound for >1 thread
  - The VMSA model from [the ESOP22
  paper](https://www.cl.cam.ac.uk/~pes20/iflat/top-extended.pdf) (`VMSA22Arm.v`)
- `ArchSemRiscV` The RISC-V instantiation of the library. This includes:
  - A User-mode axiomatic model (`UMAxRiscV.v`)
- `ArchSemX86` The x86 instantiation of the library.
- `Extraction` contains machinery to extract the code to OCaml, for now it is
  mainly use to check that the code _can_ be extracted rather than as an
  actually usable OCaml library

## Documentation

To build the documentation call `dune build @doc` and then the documentation
will be generated in:

- `_build/default/Common/ASCommon.html/toc.html`
- `_build/default/ArchSem/ArchSem.html/toc.html`
- `_build/default/ArchSemArm/ArchSemArm.html/toc.html`
- `_build/default/ArchSemRiscV/ArchSemRiscV.html/toc.html`
- `_build/default/ArchSemX86/ArchSemX86.html/toc.html`


## Current limitations

Developing complete architectural models is an ambitious long-term goal. The
curent state takes many important steps towards that, but there is still much to
do. In the short term, this includes:

### Test runner

While most of the code can run in Rocq with `vm_compute` we currently do not
have a good working extraction pipeline, or a CLI frontend to call models on
litmus tests.

### Partiality handling

In order to allow axiomatic models to define the consistency of partial
executions that contain partially executed instructions, we need to add more
support from the interface to bound what a partially executed instruction can do
next. Concurrency models must therefore correctly understand this information to
handle undefined behaviour properly.

### Intra-instruction parallelism

Currently, the interface and instruction semantics is based on the instruction
semantics being a free monad, which totally orders all the effects that an
instruction can emit. We need to relax that constraint to allow instructions to
emit multiple effects in parallel. We have a plan for an "async monad" to
replace the free monad that would enable this

## Git history

Commits before 2024-12-19 were extracted with `git filter-repo` from a private
repository and were kept for `git blame` but might not build except for the most
recent ones.
