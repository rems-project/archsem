(** This file is the top level of the SSCCommon library. Users should just
    Require Import SSCCommon.Common.
 *)

From Hammer Require Export Tactics.
Require Export bbv.Word.
Require Import DecidableClass.
From stdpp Require Export strings.
From stdpp Require Export fin.
From stdpp Require Export vector.
From stdpp Require Export finite.
From stdpp Require Export relations.
Require Export Ensembles.

Require Export CBase.
Require Export CBool.
Require Export CList.
Require Export CBitvector.
Require Export CSets.
Require Export CMaps.
Require Export CInduction.

(*** Utility functions ***)

(** Update a function at a specific value *)
Definition fun_add {A B} {_: EqDecision A} (k : A) (v : B) (f : A -> B) :=
  fun x : A => if k =? x then v else f x.


(*** Ensembles ***)
(* I really don't understand why this is not in stdpp *)
(* stdpp use propset instead of Ensemble, maybe that would be better *)

Global Instance Ensemble_elem_of {A} : ElemOf A (Ensemble A) := fun x P => P x.

Global Instance Ensemble_empty {A} : Empty (Ensemble A) := fun a => False.

Global Instance Ensemble_singleton {A} :
  Singleton A (Ensemble A) := fun x y => x = y.

Global Instance Ensemble_union {A} :
  Union (Ensemble A) := fun P Q x => P x \/ Q x.
Global Instance Ensemble_intersection {A} :
  Intersection (Ensemble A) := fun P Q x => P x /\ Q x.

Global Instance Ensemble_difference {A} :
  Difference (Ensemble A) := fun P Q x => P x /\ ¬(Q x).


Global Instance Ensemble_mbind : MBind Ensemble := λ A B f E b,
    ∃'a ∈ E, b ∈ f a.

Global Instance Ensemble_omap : OMap Ensemble := λ A B f E b,
    ∃'a ∈ E, f a = Some b.


Definition Ensemble_from_set {A C} `{ElemOf A C} (c : C) : Ensemble A := fun a => a ∈ c.

Global Instance Ensemble_SemiSet A : SemiSet A (Ensemble A).
Proof. sauto l:on. Qed.

Global Instance Ensemble_Set A : Set_ A (Ensemble A).
Proof. sauto l:on. Qed.


(*** Vectors ***)

(* This is purposefully not in stdpp because Coq does not apply it automatically
   because of dependent types. This can be solved with a Hint Resolve *)
Global Instance vector_insert {n} {V} : Insert (fin n) V (vec V n) := vinsert.
Global Hint Resolve vector_insert : typeclass_instances.

Create HintDb vec discriminated.

#[global] Hint Rewrite @lookup_fun_to_vec : vec.
#[global] Hint Rewrite @vlookup_map : vec.
#[global] Hint Rewrite @vlookup_zip_with : vec.

(* There are probably lots of other lemmas to be added here,
   I'll do case by case. *)


(*** Finite decidable quantifiers ***)

(* TODO maybe express with a decidable instance instead : There are consequences
   for extraction though *)

Definition fforallb {A : Type} `{Finite A} (P : A -> bool) : bool :=
  forallb P (enum A).

Lemma fforallb_brefl A `{Finite A} (P : A → bool):
  is_true (fforallb P) ↔ forall x : A, P x.
Proof. unfold fforallb. sauto lqb:on dep:on simp+: unfold_cqual. Qed.
#[global] Hint Rewrite fforallb_brefl : brefl.
Opaque fforallb.

Definition fexistsb {A : Type} `{Finite A} (P : A -> bool) : bool :=
  existsb P (enum A).

Lemma fexistsb_brefl A `{Finite A} (P : A → bool):
  is_true (fexistsb P) ↔ exists x : A, P x.
Proof. unfold fexistsb. sauto lqb:on dep:on simp+: unfold_cqual. Qed.
#[global] Hint Rewrite fforallb_brefl : brefl.
Opaque fexistsb.
