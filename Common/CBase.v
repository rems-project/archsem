
From stdpp Require Export base.
From stdpp Require Export tactics.
Require Import DecidableClass.
Require Export Relations.
From RecordUpdate Require Export RecordSet.
From Hammer Require Export Tactics.
Require Import ZArith.


(*** Notations ***)


(** Functional pipe notation.

    TODO figure out a correct parsing level. Currently is just below relation so
    that a = b |> f will be parsed as a = (b |> f). *)
Notation "v |> f" := (f v) (at level 69, only parsing, left associativity).

(** Monadic bind with an explicit monad annotation *)
Notation "x ←@{ M } y ; z" := (@mbind M _ _ _ (λ x : _, z) y)
  (at level 20, y at level 100, z at level 200, only parsing) : stdpp_scope.
Notation "' x ←@{ M } y ; z" := (@mbind M _ _ _ (λ x : _, z) y)
  (at level 20, x pattern, y at level 100, z at level 200, only parsing) : stdpp_scope.


(*** Utility functions ***)

(** Convenient iff destruction *)
Definition iffLR {A B : Prop} (i : A <-> B) : A -> B := proj1 i.
Definition iffRL {A B : Prop} (i : A <-> B) : B -> A := proj2 i.

(** Convert a true proposition into a rewriting rule of that proposition to true
*)
Definition Prop_for_rewrite {P : Prop} (H : P) : P <-> True.
  firstorder.
Defined.

Definition setv {R T} (proj : R -> T) {_ : Setter proj} ( v: T) : R -> R :=
  set proj (fun _ => v).

(** This allows to use set fst and set snd on pairs *)
#[global] Instance eta_pair A B : Settable (A * B) :=
  settable! (fun (a : A) (b : B) => (a, b)) <fst;snd>.


(*** Constrained quantifiers ***)

Notation "∀' x ∈ b , P" := (forall x, x ∈ b -> P)
  (at level 200, x binder, right associativity,
  format "'[ ' '[ ' ∀' x  ∈  b ']' ,  '/' P ']'") : type_scope.

(* The formatting, doesn't work so this is still printed as exists x, x ∈ b /\ P
   but that's not really a problem *)
Notation "∃' x ∈ b , P" := (exists x, x ∈ b /\ P)
  (at level 200, x binder, right associativity,
  format "'[ ' '[ ' ∃' x  ∈  b ']' ,  '/' P ']'") : type_scope.


(*** Relations ***)

Arguments clos_refl_trans {_}.


(*** Utility tactics ***)

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

(*** Integer lattice ***)

#[global] Instance join_nat : Join nat := Nat.max.
#[global] Instance meet_nat : Meet nat := Nat.min.
#[global] Instance join_pos : Join positive := Pos.max.
#[global] Instance meet_pos : Meet positive := Pos.min.
#[global] Instance join_N : Join N := N.max.
#[global] Instance meet_N : Meet N := N.min.
#[global] Instance join_Z : Join Z := Z.max.
#[global] Instance meet_Z : Meet Z := Z.min.
