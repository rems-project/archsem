
From stdpp Require Export base.
From stdpp Require Export tactics.
Require Import DecidableClass.
Require Export Relations.


(********** Notations **********)


(** Functional pipe notation.

    TODO figure out a correct parsing level. Currently is just below relation so
    that a = b |> f will be parsed as a = (b |> f). *)
Notation "v |> f" := (f v) (at level 69, only parsing, left associativity).


(********* Utility functions **********)

(** Convenient iff destruction *)
Definition iffLR {A B : Prop} (i : A <-> B) : A -> B := proj1 i.
Definition iffRL {A B : Prop} (i : A <-> B) : B -> A := proj2 i.

(** Convert a true proposition into a rewriting rule of that proposition to true
*)
Definition Prop_for_rewrite {P : Prop} (H : P) : P <-> True.
  firstorder.
Defined.

(********** Constrained quantifiers **********)


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


(********** Relations **********)

Arguments clos_refl_trans {_}.


(********** Utility tactics **********)

Ltac block t := change t with (block t) in *.
Ltac unblock := unfold block in *.

(* useful for debugging *)
Ltac deintro :=
  match goal with
  | H : _ |- _ => generalize dependent H
  end.
Ltac deintros := repeat deintro.
Ltac print_full_goal := try(deintros; match goal with |- ?G => idtac G end; fail).

(* run tac on all hypotheses in first-to-last order *)
Ltac forall_hyps tac :=
  lazymatch goal with
  | H : _ |- _ => revert H; try (forall_hyps tac); intro H; try(tac H)
  end.
