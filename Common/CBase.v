
From stdpp Require Export base.
Require Import DecidableClass.
Require Import Ensembles.


(********** Notations **********)


(** Functional pipe notation.

    TODO figure out a correct parsing level. Currently is just below relation so
    that a = b |> f will be parsed as a = (b |> f). *)
Notation "v |> f" := (f v) (at level 69, only parsing, left associativity).


(********* Utility functions **********)

(** Convenient iff destruction *)
Definition iffLR {A B : Prop} (i : A <-> B) : A -> B := proj1 i.
Definition iffRL {A B : Prop} (i : A <-> B) : B -> A := proj2 i.

(********** Constrained quantifiers **********)

Global Instance Ensembles_elem_of {A} : ElemOf A (Ensemble A) := fun x P => P x.

Definition forall_elem_of `{ElemOf A B} (P : A -> Prop) (b : B) :=
  forall x : A, x ∈ b -> P x.

Notation "∀' x ∈ b , P" := (forall_elem_of (fun x => P) b)
  (at level 200, x binder, right associativity,
  format "'[ ' '[ ' ∀' x  ∈  b ']' ,  '/' P ']'") : type_scope.

Definition exists_elem_of `{ElemOf A B} (P : A -> Prop) (b : B) :=
  exists x : A, x ∈ b /\ P x.

Notation "∃' x ∈ b , P" := (exists_elem_of (fun x => P) b)
  (at level 200, x binder, right associativity,
  format "'[ ' '[ ' ∃' x  ∈  b ']' ,  '/' P ']'") : type_scope.

Tactic Notation "unfold_cqual" :=
  repeat unfold forall_elem_of in *;
  repeat unfold exists_elem_of in *.

Global Hint Unfold forall_elem_of : cqual.
Global Hint Unfold exists_elem_of : cqual.
