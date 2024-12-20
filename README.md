# ArchSem

ArchSem is a Rocq framework to define the semantics of CPU architectures
such as Arm-A, RISC-V, and x86, integrating their concurrency and instruction-set semantics.
The framework is designed to be generic, but so far is only instantiated for Arm-A.


## General goals and organization

In order to build an architecture model one needs two components:
- An _ISA model_ that provides the semantics of instructions. Those are intended
  to be derived from [Sail](https://github.com/rems-project/sail) or
  [ASL](https://developer.arm.com/Architectures/Architecture%20Specification%20Language)
  specifications such as [sail-arm](https://github.com/rems-project/sail-arm) (via Sail).
  We are currently working on a path to extract those from Sail, which is not
  fully operational yet.
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

ArchSem defines an [_Interface_](ISASem/Interface.v) between the two so
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
  extraction pipeline and utilities to parse litmus tests to run.
- The interface must support all kinds of concurrency models: axiomatic,
  micro-architectural operations, promising, etc.
- All models can be partial, so the framework must handle partiality properly.
  ISA models can fail at any point and those failures must be correctly propagated
  upwards. 

## Building

See [INSTALL.md](INSTALL.md) for dependencies, installation, and build
instructions.

## Rocq automation

There are some powerful custom tactics in `Common`. TODO write documentation for
them.

## The current state and directory structure

The directory structure is intended to change soon, so don't rely on it too much

- `Common` (Rocq module name `ASCommon`) is the "utils" library. It contains all
  non-ArchSem-specific Rocq lemmas and automation, as well as required theories
  such that executable relational algebra or effects and free monads
- `ISASem` The definition of the interface between ISA model and concurrency
  models generically, as well as the definition of the module type an
  architecture must instantiate to work with this framework. This also contain
  our current hackish Arm Instantiation (to be replaced soon)
- `GenModels` The definition of what a CPU architecture model is, as well as the
  definition of what an execution trace is over multiple CPU core (Candidate
  executions). This also contains a definition of a sequential model for Arm
- `promising-arm` The definition of a User-mode Promising model for Arm (from
  [the PLDI19 paper](https://sf.snu.ac.kr/publications/promising-arm-riscv.pdf),
  as well as a WIP VM Promising model.
- `AxiomaticModels` This defines 3 axiomatic models for Arm: Sequential
  Consistent (unsound for more than 1 thread but useful for comparisons), a
  regular User-mode only model and the VMSA model from [the ESOP22
  paper](https://www.cl.cam.ac.uk/~pes20/iflat/top-extended.pdf). We also have
  the core part of the proof of equivalence between the last 2 models.
- `Extraction` contains machinery to extract the code to OCaml, for now it is
  mainly use to check that the code _can_ be extracted rather than as an
  actually usable OCaml library

## Documentation

To build the documentation call `dune build @doc` and then the documentation
will be generated in:

- `_build/default/Common/ASCommon.html/toc.html`
- `_build/default/ISASem/ISASem.html/toc.html`
- `_build/default/GenModels/GenModels.html/toc.html`
- `_build/default/AxiomaticModels/AxiomaticModels.html/toc.html`
- `_build/default/promising-arm/PromisingArm.html/toc.html`


## Current limitations

Developing complete architectural models is an ambitious long-term goal.  The curent state takes many important steps towards that, but there is still much to do. In the short term, this includes:

### Connection to Sail

We have almost all of the pipeline to import a Sail model into ArchSem done, but
some details remain.

### Test runner

While most of the code can run in Rocq we currently do not have a good working
extraction pipeline, or a CLI frontend to call models on litmus
tests. 

### Partiality handling

In order to allow partial models and execution traces that contain partially
executed instructions, we need more support from the interface to bound what a
partially executed instruction can do next. Concurrency models must therefore correctly
understand this information to handle undefined behaviour properly.

### Intra-instruction parallelism

Currently, the interface and instruction semantics is based on the instruction
semantics being a free monad, which totally orders all the effects that an
instruction can emit. We need to relax that constraint to allow instructions to
emit multiple effects in parallel. This cannot be achieved with
non-deterministic interleaving because of intricate details on relaxed
architectures like Arm.

## Git history

Commits before 2024-12-19 were extracted with `git filter-repo` from a private
repository and were kept for `git blame` but might not build except for the most
recent ones.
