# Operational/axiomatic sequential refinement proof
# THIS IS AN OLD, FORKED VERSION OF ARCHSEM ONLY USED FOR THIS VERY SPECIFIC PROOF

**For the actual, up-to-date ArchSem refer to the main supplemented archive.**
This development should only be used to inspect the proof that the operational
sequential model refines the SC axiomatic model.

The proof can be found in [ArchSemArm/CDestruct.v](ArchSemArm/ArmSeqAxOpEq.v).

## Building

See [INSTALL.md](INSTALL.md) for dependencies, installation, and build
instructions.

## Rocq automation

There are some powerful custom tactics in `Common`, as well as useful but
generic library. See the [README](Common/README.md) there for more details. In
particular `cdestruct` is in [Common/CDestruct.v](Common/CDestruct.v).



## Documentation

To build the documentation call `dune build @doc` and then the documentation
will be generated in:

- `_build/default/Common/ASCommon.html/toc.html`
- `_build/default/ArchSem/ArchSem.html/toc.html`
- `_build/default/ArchSemArm/ArchSemArm.html/toc.html`
