(** This file is the top level of the SSCCommon library. Users should just
    Require Import SSCCommon.Common.
 *)

From Hammer Require Export Tactics.
From RecordUpdate Require Export RecordSet.
Require Export bbv.Word.
Require Import DecidableClass.
From stdpp Require Export strings.
From stdpp Require Export fin.
From stdpp Require Export vector.
From stdpp Require Export finite.
Require Export Ensembles.

Require Export CBase.
Require Export CBool.
Require Export CList.
Require Export CBitvector.

(********** Utility functions **********)

(** Update a function at a specific value *)
Definition fun_add {A B} {_: EqDecision A} (k : A) (v : B) (f : A -> B) :=
  fun x : A => if k =? x then v else f x.


(********** Ensembles **********)

(* TODO: Move to stdpp *)
Global Instance Ensemble_elem_of {A} : ElemOf A (Ensemble A) := fun x P => P x.

(* TODO: Move to stdpp *)
Global Instance Ensemble_omap : OMap Ensemble := λ A B f E b,
    ∃'a ∈ E, f a = Some b.

(* TODO: Move to stdpp *)
Global Instance Ensemble_empty {A} : Empty (Ensemble A) := fun a => False.

Definition Ensemble_from_list {A} (l : list A) : Ensemble A := fun a => a ∈ l.


(********** Vectors **********)

(* This is purposefully not in stdpp because Coq does not apply it automatically
   because of dependent types. This can be solved with a Hint Resolve *)
Global Instance vector_insert {n} {V} : Insert (fin n) V (vec V n) := vinsert.
Global Hint Resolve vector_insert : typeclass_instances.

Create HintDb vec discriminated.

#[global] Hint Rewrite @lookup_fun_to_vec : vec.
#[global] Hint Rewrite @vlookup_map : vec.
#[global] Hint Rewrite @vlookup_zip_with : vec.

(* There are probably lots of other lemmas to be added here,
   I'll do case by case.
 *)


(********** Finite decidable quantifiers **********)

Definition fforallb {A : Type} `{Finite A} (P : A -> bool) : bool :=
  forallb P (enum A).

Lemma fforallb_brefl A `{Finite A} (P : A → bool):
  is_true (fforallb P) ↔ forall x : A, P x.
Proof. unfold fforallb. sauto lqb:on dep:on simp+: unfold_cqual. Qed.
#[global] Hint Rewrite fforallb_brefl : brefl.


Definition fexistsb {A : Type} `{Finite A} (P : A -> bool) : bool :=
  existsb P (enum A).

Lemma fexistsb_brefl A `{Finite A} (P : A → bool):
  is_true (fexistsb P) ↔ exists x : A, P x.
Proof. unfold fexistsb. sauto lqb:on dep:on simp+: unfold_cqual. Qed.
#[global] Hint Rewrite fforallb_brefl : brefl.
