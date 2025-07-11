# ArchSem style guide

The base of ArchSem style is the [Iris
style-guide](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/style_guide.md)
which should be used as a referenced. There are some differences though.

Not all the current code conforms to this style guide, but all new code should.
Do not mix style updating changes and semantic changes in a single commit.
(ArchSem does squash PR merging: one PR means one commit). One can and should do
style fixing of code that is also semantically changed.

## Difference with Iris/stdpp style

### Use of `Theorem`

We are happy to use `Theorem` for the one important theorem of a file. `Lemma`
should be used for any other proof.

### Match indentation

We indent match bodies by 4 spaces:

```coq
match a with
| Constructor =>
    the_body
end
```

## ArchSem extra style rules

### Module Imports and stateful code

When importing non-file module for notations or hints/typeclass instances, and
when setting Rocq flags, it should always be done at the beginning of the file
or section. This minimizes the number of location to look for behaviour changing
options setting and module importing.

### Proof length

This is not always applicable, but if a proof script is longer than 50 lines,
consider splitting it into sub-lemmas.

### `;` vs `all:`

If a proof is terminated by a single composed tactic `tactic1; tactic2; tactic3`,
then consider doing:
```coq
  tactic1.
  all: tactic2.
  all: tactic3.
```

This allows proof readers to step through more easily without changing the code.

### `Lemma` vs `Definition`

In general constants introduced by `Lemma` should be in `Prop` and `Qed`-opaque.
No proof term should be made transparent unless very special cases for
fixpoint reductions. In particular one should not try to make equality proofs
transparent to reduce transports, they should use `CTrans` instead.
