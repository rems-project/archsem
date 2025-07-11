# ArchSem Common files and libraries

This directly contains a set of Rocq library and lemmas that are not specific to
ArchSem but could be more widely used. It's a some "standard" library extension
on top of `stdpp`.

The goal is that all lemmas that are not specific to ArchSem end-up here, as
well as all generic proof-automation, notations, and type classes.

This could either things that could be exported to one of the used libraries
like `stdpp`, `stdpp-bitvector`, `hammer-tactics`, `coq-equations`, ... or
things required to make multiple libraries interact together.

ArchSem aim to be easily interoperable with the Iris ecosystem, that is why
`stdpp` is intended to be the main focus, in particular when there is two
versions of a concept in multiple sources we will try to use the stdpp one. In
such a case `ASCommon` will try to define lemmas and proof-automation to get as
smooth as possible interoperability with any other versions of the concept (if
that's not already done in `stdpp`).

We'll try to present the main components of `ASCommon` in this document, as well
the general expected Rocq style and way of doing things of this project.

## Coding style

- We use Unicode symbols everywhere as the `stdpp`/`iris` ecosystem: for example
  `∀` and not `forall`. Some old code doesn't do this, so we fix when we do any
  change in the area
- We try to respect column 80 (82/83 is fine if it looks much better, but don't
  abuse it)
- We put space on both sides of the colon: `(a : A)`
- Proofs are either a one-liner `Proof. tactics... Qed.` or `Proof` and `Qed`
  are on separate line
- We don't use SSReflect for now, unless someone gives a good argument for it

## Axioms, defaults and discipline

ArchSem works in classical logic with functional and propositional
extensionality. This also induce proof irrelevance and critically UIP.

The general mindset of this project is to work _as if_ OTT (Observational Type
Theory) existed in Rocq, while maintaining `Type` as an executable sort. In
practice this means that axioms are only in `Prop` and `Prop` is used as if it
was `SProp` which means `Prop` cannot be destroyed into `Type` except if it's
`False`. This means that terms in `Type` should compute inside Rocq and extract
to executable function in Ocaml. That also means that basically any
definition/lemma in `Prop` should be `Qed` and not `Defined`.

Typeclass resolution assumes all constants are `Opaque` by default, use
`Typeclasses Transparent` if you need transparent behaviour.

## Computable transport

The previous system prevents us from writing a general transport function
`transport (T U : Type) (e : T = U) (t : T) : U`. However, in practice we (in
this project) only need transports on indexed type families such as `fin` or
`vec`. Therefore, we have a `CTrans` typeclass to provide computable transport
for all those type families based on equalities on some index.
```coq
Class CTrans {T : Type} (F : T → Type) :=
  ctrans : ∀ (x y : T) (eq : x = y) (a : F x), F y.
```

## CDestruct

The main automation tactic specific to this project is
[`cdestruct`](CDestruct.v) which is an extensible variant of Rocq's `intuition`
or Isabelle's `clarify`. See the file for details. Roughly, it performs the job of
`intuition`, `discriminate`, `contradiction`, `simplify_eq`, `case_split`
all-in-one in an extensible manner.

## CInduction

The base induction tactic is terrible at using induction principle about
non-inductive types and predicates, so we make [`cinduction`](CInduction.v) to
handle that. So far it mostly just does the job of `elim` and not really
`induction` as it does not handle any convoy pattern, or automatic
generalizations. Some mashup of this tactic and Equations' tactic could be made
in the future to handle that.

## Boolean and Decidable predicate

Generally in this development we try to define decidable predicate in `Prop` and
then provide a `Decision` instance (from `stdpp`). However to handle boolean
reflection we have a `BooleanUnfold` rewrite typeclass to unfold all boolean
statement back into `Prop`. We use `Is_true` as the `bool` to `Prop` coercion as
`stdpp`. See [CBool.v](CBool.v) for more details.

## Arithmetic and bitvectors

Generally we try to use `N` and `Z` in new stuff and forget `nat` unless really
needed for dependent stuff. So far we use `fin` (`Fin.t`) but we're thinking of
moving to `{ n : N | n < m}`. In addition `fin n` is interpreted as $[0; n - 1]$
and not $[1 ; n]$ here and there is coercion into `nat` that does that.

We use `stdpp-bitvector` for bitvectors, therefore try to use `N` for anything that
might be related to bitvector sizes.

## Containers: lists, sets, maps, relations.

We use standard library list and fixed-size vector `vec` (`Vector.t`) for now.
We keep using `nat` indexing (and length) when working with those.

We use all the set and maps infrastructure from `stdpp` and we define
[GRel](GRel.v) a library for executable relational algebra on gsets of pairs.

We use the notations `∀ x ∈ s, P x` and `∃ x ∈ s, P x` when working with sets or
lists.

In addition to the general `SetUnfold` we define `FMapUnfold`, `LookupUnfold`
and `LookupTotalUnfold` for unfolding `fmap` `(!!)` and `(!!!)` over composed
structure.

## Monads and effects

We reuse the monad typeclasses of `stdpp` so far (that are universe
monomorphic). We define our own concept of [Effects](Effects.v) with a new monad
typeclass `MCall` for calling an effect in a monad. We then define the following
monads and transformers that are not in `stdpp`.
- [result](CResult.v) monad with error aka OCaml/Rust result type (Ok or Error)
- [Exec](Exec.v): monad with error, non-determinism and state.
- [fMon](FMon.v): free monad of a set of effects.
- [cMon](FMon.v): Choice monad of a set of effects: free monad with non-free
  non-determinism
- [stateT](StateT.v): A state monad transformer.

