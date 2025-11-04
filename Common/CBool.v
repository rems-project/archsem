(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zongyuan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
(*                                                                            *)
(*  All files except SailArmInstTypes.v are distributed under the             *)
(*  license below (BSD-2-Clause). The former is distributed                   *)
(*  under a mix of BSD-2-Clause and BSD-3-Clause Clear, as described          *)
(*  in the file header.                                                       *)
(*                                                                            *)
(*                                                                            *)
(*  Redistribution and use in source and binary forms, with or without        *)
(*  modification, are permitted provided that the following conditions        *)
(*  are met:                                                                  *)
(*                                                                            *)
(*   1. Redistributions of source code must retain the above copyright        *)
(*      notice, this list of conditions and the following disclaimer.         *)
(*                                                                            *)
(*   2. Redistributions in binary form must reproduce the above copyright     *)
(*      notice, this list of conditions and the following disclaimer in the   *)
(*      documentation and/or other materials provided with the distribution.  *)
(*                                                                            *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS       *)
(*  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT         *)
(*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS         *)
(*  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE            *)
(*  COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,      *)
(*  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,      *)
(*  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS     *)
(*  OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND    *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR     *)
(*  TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE    *)
(*  USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.  *)
(*                                                                            *)
(******************************************************************************)

(** This module cover all thing related to uses of boolean, mainly as decidable
    proposition.

    In particular it will cover boolean reflection and decidable generic
    operations like equality. *)
From Stdlib Require Import DecidableClass JMeq.

Require Import Equations.Prop.Equations.

From stdpp Require Import base.
From stdpp Require Export decidable.
From stdpp Require Export sets.
From Hammer Require Import Tactics.
From Hammer Require Reflect.

Require Import Options.
Require Import CBase.
Require Import CDestruct.


(** Add a few lemma to the brefl rewrite database *)
Lemma true_is_true (b : bool) : b ↔ is_true b.
Proof. destruct b; naive_solver. Qed.
#[export] Hint Rewrite <- true_is_true : brefl.

Lemma true_eq_true (b : bool) : b ↔ b = true.
Proof. destruct b; naive_solver. Qed.
#[export] Hint Rewrite <- true_eq_true : brefl.

Lemma not_eq_false (b : bool) : ¬ b ↔ b = false.
Proof. destruct b; naive_solver. Qed.
#[export] Hint Rewrite <- not_eq_false : brefl.

(** * Bool unfold ***)

(* This an attempt to have a custom boolean unfolding, to not need to handle the
   mess with having both is_true and Is_true coercion. *)

Class BoolUnfold (b : bool) (P : Prop) :=
  {bool_unfold : b <-> P }.
Global Hint Mode BoolUnfold ! - : typeclass_instances.

Global Instance BoolUnfold_proper :
  Proper (eq ==> iff ==> iff) BoolUnfold.
Proof. solve_proper2_tc. Qed.

Ltac get_bool_unfold_evars _ :=
  lazymatch goal with
  | |- BoolUnfold ?G _ => G
  end.

Tactic Notation "bool_unfold" :=
  rewrite @bool_unfold; [ | block_all_evars get_bool_unfold_evars; tc_solve];
  unblock_evars.
Tactic Notation "bool_unfold" "in" ident(h) :=
  rewrite @bool_unfold in h; [ | block_all_evars get_bool_unfold_evars; tc_solve];
  unblock_evars.


(* Explain to coq hammer tactic how to use Is_true and BoolUnfold *)
#[export] Hint Rewrite @bool_unfold using typeclasses eauto : brefl.


(* Basic implementation of BoolUnfold *)
Global Instance bool_unfold_default (b : bool) :
  BoolUnfold b b | 1000.
Proof. done. Qed.

Global Instance bool_unfold_false : BoolUnfold false False.
Proof. done. Qed.

Global Instance bool_unfold_true : BoolUnfold true True.
Proof. done. Qed.

Global Instance bool_unfold_and (b b' : bool) P Q :
  BoolUnfold b P -> BoolUnfold b' Q ->
  BoolUnfold (b && b') (P /\ Q).
Proof. tcclean. destruct b; destruct b'; naive_solver. Qed.

Global Instance bool_unfold_or (b b' : bool) P Q :
  BoolUnfold b P -> BoolUnfold b' Q ->
  BoolUnfold (b || b') (P \/ Q).
Proof. tcclean. destruct b; destruct b'; naive_solver. Qed.

Global Instance bool_unfold_not (b : bool) P :
  BoolUnfold b P ->
  BoolUnfold (negb b) (¬ P).
Proof. tcclean. destruct b; naive_solver. Qed.

Global Instance bool_unfold_implb (b b' : bool) P Q :
  BoolUnfold b P -> BoolUnfold b' Q ->
  BoolUnfold (implb b b') (P -> Q).
Proof. tcclean. destruct b; destruct b'; naive_solver. Qed.

Global Instance bool_unfold_iff (b b' : bool) P Q :
  BoolUnfold b P -> BoolUnfold b' Q ->
  BoolUnfold (eqb b b') (P <-> Q).
Proof. tcclean. destruct b; destruct b'; naive_solver. Qed.

Global Instance bool_unfold_bool_decide `{Decision P} :
  BoolUnfold (bool_decide P) P.
Proof. tcclean. destruct (decide P); naive_solver. Qed.

Global Instance bool_unfold_pair A B c (b : A → B → bool) P:
  (∀ x y, BoolUnfold (b x y) (P x y)) →
  BoolUnfold (let '(x, y) := c in b x y) (let '(x, y) := c in P x y).
Proof. by destruct c. Qed.

Definition bool_unfold_reflect  `(r : reflect P b) : BoolUnfold b P.
Proof. tcclean. destruct r; naive_solver. Qed.

#[global] Instance bool_unfold_Z_leb z z' :
  BoolUnfold (z <=? z')%Z (z ≤ z')%Z := bool_unfold_reflect (Z.leb_spec0 z z').

#[global] Instance bool_unfold_Z_le z z' :
  BoolUnfold (z <? z')%Z (z < z')%Z := bool_unfold_reflect (Z.ltb_spec0 z z').



(** * Decidable propositions ***)

Ltac unfold_decide :=
  match goal with
    |- Decision ?t =>
      let h := get_head t in unfold h; apply _
  end.

Section ProperDecision.
  Import CMorphisms.

  (** Magic that allow rewriting in decision instances using ↔
      Might be slow, so you might need to use it by hand *)
  Global Instance Proper_Decision :
    Proper (iff ==> (flip arrow)) Decision.
  Proof using.
    intros x y H []; [left | right]; abstract naive_solver.
  Defined.
End ProperDecision.

Ltac pair_let_clean_Decision :=
  match goal with
    |- context G [(let '(x, y) := _ in _)] =>
      eapply Proper_Decision;[
        pair_let_clean; reflexivity
      |]
  end.
#[export] Hint Extern 10 (Decision _) =>
  pair_let_clean_Decision : typeclass_instances.


(** * Equality decision *)

(** Decidable equality notation that use [Decision] *)
Notation "x =? y" := (bool_decide (x = y)) (at level 70, no associativity)
    : stdpp_scope.

(** JMeq simplification lemma *)
Lemma JMeq_simpl A (a b : A) : a =ⱼ b ↔ a = b.
Proof. use JMeq_eq. naive_solver. Qed.

(** Finds a equality but searches a bit more than [TCEq] *)
Class TCFindEq {A} (x : A) (y : A) : Prop := tc_find_eq : x = y.
Global Hint Mode TCFindEq + + + : typeclass_instances.
#[global] Instance TCFindEq_refl A (x : A) : TCFindEq x x.
Proof. done. Qed.
Global Hint Extern 1 (TCFindEq ?x ?y) => (unfold TCFindEq in *; fast_done) : typeclass_instances.
Global Hint Extern 2 (TCFindEq ?x ?y) => (unfold TCFindEq in *; congruence) : typeclass_instances.

(** Stupid but useful *)
#[global] Instance Empty_set_eq_dec : EqDecision ∅.
Proof. intros []. Defined.

(** ** Dependent equality decision *)
(** Decidable heterogeneous equality in the case the dependencies are equal.
    This is base building block for equality decision procedure of dependent
 types *)
Class EqDepDecision {A} (P : A → Type) :=
  eqdep_decide : ∀ {a b : A} (H : a = b) (x : P a) (y : P b), Decision (x =ⱼ y).

#[global] Instance eq_dep_decision_f_equal A `{EqDepDecision B P} (f : A → B) :
  EqDepDecision (λ x, P (f x)) :=  λ a b H x y, eqdep_decide (f_equal f H) x y.

(* compose is opaque, hence we need another instance *)
#[global] Instance eq_dep_decision_compose A `{EqDepDecision B P} (f : A → B) :
  EqDepDecision (P ∘ f) := eq_dep_decision_f_equal A f.

#[global] Instance eq_dep_decision_dec `{EqDepDecision A P}
  (a b : A) {H : TCFindEq a b} (x : P a) (y : P b) : Decision (x =ⱼ y) :=
  eqdep_decide H x y.

Equations fin_eqdep_dec : EqDepDecision fin :=
  fin_eqdep_dec _ _ _ 0%fin 0%fin := left _;
  fin_eqdep_dec _ _ _ (FS _) 0%fin := right _;
  fin_eqdep_dec _ _ _ 0%fin (FS _) := right _;
  fin_eqdep_dec _ _ H (FS a) (FS b) := dec_if (fin_eqdep_dec _ _ (Nat.succ_inj _ _ H) a b).
Solve All Obligations with
  (intros;
   unfold TCFindEq in *;
   simplify_eq /=;
     rewrite JMeq_simpl in *;
   naive_solver).
#[export] Existing Instance fin_eqdep_dec.

Class EqDep2Decision {A B} (P : A → B → Type) :=
  eqdep2_decide : ∀ {a a' : A} (Ha : a = a') {b b' : B} (Hb : b = b') (x : P a b) (y : P a' b'), Decision (x =ⱼ y).

#[global] Instance eq_dep2_decision_dec `{EqDep2Decision A B P}
  (a a' : A) {H : TCFindEq a a'} (b b' : B) {H' : TCFindEq b b'} (x : P a b) (y : P a' b') : Decision (x =ⱼ y) :=
  eqdep2_decide H H' x y.

(** ** Record equality decision *)

Ltac decide_field a b tac :=
  tryif unify a b then idtac else
    ((destruct decide (a = b)
      || (odestruct (@decide (a = b)) ; [shelve | |])
      || destruct decide (a =ⱼ b)
      || (odestruct (@decide (a =ⱼ b)); [shelve | |])) ;
     [ | right; abstract tac
    ]).

Ltac decide_fields l r right_tac :=
  tryif unify l r then idtac else
    lazymatch l with
    | ?C ?a =>
        lazymatch r with
        | ?C' ?a' =>
            decide_fields C C' right_tac;
            decide_field a a' right_tac
        | _ => right; abstract right_tac
        end
    | _ => right; abstract right_tac
    end.

Ltac decide_eq :=
    lazymatch goal with
    | |- Decision (?l = ?r) =>
        unshelve
          (decide_fields l r
             ltac:((injection as [=] || intro); by simplify_eq);
           left; abstract (subst; reflexivity))
    end.

Ltac decide_jmeq :=
  lazymatch goal with
  | |- Decision (?l =ⱼ ?r) =>
      unshelve
        (decide_fields l r
           ltac:(subst; rewrite JMeq_simpl in *; (injection as [=] || intro); by simplify_eq);
         left; abstract (subst; reflexivity))
  end.

(** ** Decision of record of propositions *)

Ltac2 rec decide_record_fields (flds : constr list) : unit :=
  match flds with
  | hd :: tl =>
      destruct (decide $hd) >
        [ | right; abstract (intros []; Std.contradiction None)];
      decide_record_fields tl
  | _ => ()
  end.

Ltac2 decide_record0 () :=
  lazy_match! goal with
  | [ |- Decision ?r] =>
      (* let head := get_head r in *)
      assert_bt (Option.equal Int.equal (get_nconstructors r) (Some 1));
      let ctr := get_constructor r 0 |> Option.get_bt in
      (* printf "%t" ctr; *)
      let (args, _) := decompose_non_dep_fun_type (Constr.type ctr) in
      (* printf "%a and %t" (prt_list prt_cstr) args t; *)
      decide_record_fields args;
      abstract (left; split > [assumption..])
  | [ |- _] => zero_tacticf "Not an Decision instance search"
  end.
Ltac2 Notation decide_record := decide_record0 ().
Tactic Notation "decide_record" := ltac2:(decide_record).

(** ** Hint database to decide equality *)
Create HintDb eqdec discriminated.

#[global] Hint Extern 3 => progress cbn : eqdec.
#[global] Hint Extern 10 (Decision (_ = _)) => decide_eq : eqdec.
#[global] Hint Extern 10 (Decision (_ =ⱼ _)) => decide_jmeq : eqdec.
#[global] Hint Extern 4 (Decision (?a =@{_ * _} _)) => is_var a; destruct a : eqdec.
#[global] Hint Extern 4 (Decision (_ =@{_ * _} ?b)) => is_var b; destruct b : eqdec.
#[global] Hint Extern 4 (Decision (?a =@{option _} _)) => is_var a; destruct a : eqdec.
#[global] Hint Extern 4 (Decision (_ =@{option _} ?b)) => is_var b; destruct b : eqdec.

#[global] Instance sigT_dec `{EqDecision A} (P : A → Type) `{EqDepDecision A P} :
  EqDecision (sigT P).
Proof. intros [] []. decide_eq. Defined.


(* Add a hint for resolving Decision of matches*)
#[export] Hint Extern 1 (Decision match ?x with _ => _ end) =>
  case x ||
    (let nx := fresh "x" in
     pose (nx := x);
     change x with nx at 1;
     case nx) : typeclass_instances.

#[export] Hint Extern 3 (Decision _) => progress cbn : typeclass_instances.

#[export] Hint Extern 1 (Decision (?a = ?b)) => eunify a b; left; reflexivity : typeclass_instances.

(** Equality with pattern. Decide equation of the form [a = Constr b c d] where
    the entire type might not have EqDecision Such as [x =@{bool + R} inl true] *)
#[export] Hint Extern 15 (Decision (?a = ?b)) =>
  let ha := get_head a in
  let hb := get_head b in
  assert_fails (is_constructor ha; is_constructor hb);
  ((is_constructor hb; destruct a) ||
   (is_constructor ha; destruct b));
  try (right; discriminate); try (left; reflexivity); autorewrite with inj : typeclass_instances.
