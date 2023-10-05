(** This file is the top level of the SSCCommon library. Users should just
    Require Import SSCCommon.Common.
 *)

From Hammer Require Export Tactics.
Require Import DecidableClass.
From stdpp Require Export strings.
From stdpp Require Export fin.
From stdpp Require Export pretty.
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


(** * Vectors ***)

Section Vector.
  Context {A : Type}.
  Context {n : nat}.

  #[global] Instance vinsert' : Insert (fin n) A (vec A n) := vinsert.

  #[global] Instance valter : Alter (fin n) A (vec A n) :=
    λ f k v, vinsert k (f (v !!! k)) v.

  Lemma vlookup_alter (k : fin n) f (v : vec A n) :
    alter f k v !!! k = f (v !!! k).
  Proof using.
    unfold alter, valter.
    rewrite vlookup_insert.
    reflexivity.
  Qed.

  Lemma valter_eq (k : fin n) f (v : vec A n) :
    f (v !!! k) = v !!! k → alter f k v = v.
  Proof using.
    unfold alter, valter.
    intros ->.
    apply vlookup_insert_self.
  Qed.


  #[global] Instance Setter_valter_wf (k : fin n) :
    @SetterWf (vec A n) A (lookup_total k) :=
    { set_wf := Setter_alter k;
      set_get := vlookup_alter k;
      set_eq := valter_eq k
    }.

End Vector.

Create HintDb vec discriminated.

#[global] Hint Rewrite @lookup_fun_to_vec : vec.
#[global] Hint Rewrite @vlookup_map : vec.
#[global] Hint Rewrite @vlookup_zip_with : vec.
#[global] Hint Rewrite @vlookup_insert : vec.
#[global] Hint Rewrite @vlookup_alter : vec.
#[global] Hint Rewrite @vlookup_insert_self : vec.
#[global] Hint Rewrite @valter_eq using done : vec.



(*** Finite decidable quantifiers ***)

(* TODO maybe express with a decidable instance instead : There are consequences
   for extraction though
   TODO: That is the new plan now: move everything to Decision.
 *)

Definition fforallb `{Finite A} (P : A -> bool) : bool :=
  forallb P (enum A).

Global Instance fforallb_unfold `{Finite A} (P : A -> bool) Q:
  (forall a : A, BoolUnfold (P a) (Q a)) ->
  BoolUnfold (fforallb P) (forall a : A, Q a).
Proof.
  tcclean.
  unfold fforallb.
  rewrite bool_unfold.
  sauto lq:on dep:on.
Qed.

Definition fexistsb `{Finite A} (P : A -> bool) : bool :=
  existsb P (enum A).

Global Instance fexistsb_unfold `{Finite A} (P : A -> bool) Q:
  (forall a : A, BoolUnfold (P a) (Q a)) ->
  BoolUnfold (fexistsb P) (exists a : A, Q a).
Proof.
  tcclean.
  unfold fexistsb.
  rewrite bool_unfold.
  sauto lq:on dep:on.
Qed.


(*** Finite number utilities ***)

(* TODO upstream to stdpp *)
Bind Scope fin_scope with fin.

Global Instance pretty_fin (n : nat) : Pretty (fin n)  :=
  (fun n => pretty (n : nat)).
Global Hint Mode Pretty ! : typeclass_instances.

Definition fin_to_N {n : nat} : fin n → N := N.of_nat ∘ fin_to_nat.
Coercion fin_to_N : fin >-> N.



(*** VectorLookup ***)
Section VecLookup.
  Context {T : Type}.
  Context {n : nat}.

  Global Instance vec_lookup_nat : Lookup nat T (vec T n) :=
    fun m v =>
      match decide (m < n) with
      | left H => Some (v !!! Fin.of_nat_lt H)
      | right _ => None
      end.

  Lemma vec_to_list_lookup (v : vec T n) m : vec_to_list v !! m = v !! m.
  Proof using.
    unfold lookup at 2.
    unfold vec_lookup_nat.
    case_decide.
    - apply vlookup_lookup'.
      naive_solver.
    - apply lookup_ge_None.
      rewrite vec_to_list_length.
      lia.
  Qed.

  Global Instance vec_lookup_nat_unfold m (v : vec T n) r:
    LookupUnfold m v r →
    LookupUnfold m (vec_to_list v) r.
  Proof using. tcclean. apply vec_to_list_lookup. Qed.

  Global Instance vec_lookup_N : Lookup N T (vec T n) :=
    fun m v => v !! (N.to_nat m).
End VecLookup.
