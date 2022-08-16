
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

(* If needed it is always good to open those as soon as possible *)
Global Hint Extern 0 => unfold forall_elem_of : cqual.
Global Hint Extern 0 => unfold exists_elem_of : cqual.


(********** Set equivalence **********)

Definition set_equiv `{SubsetEq E} : Equiv E := fun e1 e2 => e1 ⊆ e2 /\ e2 ⊆ e1.
Infix "≡ₛ" := set_equiv (at level 70, no associativity) : stdpp_scope.

Notation "(≡ₛ)" := set_equiv (only parsing) : stdpp_scope.
Notation "( x ≡ₛ.)" := (set_equiv x) (only parsing) : stdpp_scope.
Notation "(.≡ₛ x )" := (λ y, y ≡ₛ x) (only parsing) : stdpp_scope.
Notation "(≢ₛ)" := (λ x y, ¬x ≡ₛ y) (only parsing) : stdpp_scope.
Notation "x ≢ₛ y":= (¬x ≡ₛ y) (at level 70, no associativity) : stdpp_scope.
Notation "( x ≢ₛ.)" := (λ y, x ≢ₛ y) (only parsing) : stdpp_scope.
Notation "(.≢ₛ x )" := (λ y, y ≢ₛ x) (only parsing) : stdpp_scope.
