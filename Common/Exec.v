(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zonguyan Liu, Aarhus University                                       *)
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

(** This file defines an execution monad for operational models.

This monad supports non determinism and errors. Use StateT to add state. *)

Require Import Options.
Require Import Common.
Require Import Effects.


(* TODO: Make it a top level name *)
Module Exec.

(** * Base definitions *)
Record res {St E A : Type} := make {
    results: list (St * A);
    errors: list (St * E);
  }.
Arguments res : clear implicits.
Arguments make {_ _ _}.

(** Decide if an execution has errors *)
Definition has_error `(e : res St E A) :=
  match e with
  | make _ [] => False
  | _ => True
  end.
#[global] Instance has_error_dec `(e : res St E A): Decision (has_error e).
Proof. unfold_decide. Qed.

(** Create an execution from a set of results, e.g. to convert from pure
    non-determinism to Exec *)
Definition Results {E A C} `{Elements A C} (s : C) : res () E A := make (map ((),.) (elements s)) [].

(** Merge the results of two executions *)
Definition merge {St E A} (e1 e2 : res St E A) :=
  make (e1.(results) ++ e2.(results)) (e1.(errors) ++ e2.(errors)).
#[global] Typeclasses Opaque merge.
Arguments merge : simpl never.

(** Convert an execution into a list of results *)
Definition to_result_list `(e : res St E A) : list (result (St * E) (St * A)) :=
  map Ok e.(results) ++ map Error e.(errors).

Definition t {St E A} := St → res St E A.
Arguments t : clear implicits.
Arguments make {_ _ _}.

#[global] Instance mret_inst {St E} : MRet (t St E) := λ _ v st, make [(st,v)] [].

#[global] Instance mbind_inst {St E} : MBind (t St E) :=
  λ _ _ f e st, foldr merge (make [] (e st).(errors)) (map (λ '(st', r), f r st') (e st).(results)).
#[global] Typeclasses Opaque mbind_inst.

#[global] Instance fmap_inst {St E} : FMap (t St E) :=
  λ _ _ f e st, make (map (λ '(st', r), (st', f r)) (e st).(results)) (e st).(errors).
#[global] Typeclasses Opaque fmap_inst.

#[global] Instance throw_inst {St E} : MThrow E (t St E) := λ _ e st, make [] [(st,e)].

#[global] Instance choose_inst {St E} : MChoose (t St E) :=
  λ '(ChooseFin n) st, make (map (st,.) (enum (fin n))) [].
#[global] Typeclasses Opaque choose_inst.

Lemma mdiscard_eq {St E A} : mdiscard =@{t St E A} (λ st, make [] []).
Proof. reflexivity. Qed.

#[global] Instance elem_of_results {E A} : ElemOf A (t () E A) :=
  λ x e, x ∈ (map snd (e ()).(results)).
#[global] Typeclasses Opaque elem_of_results.

#[global] Instance elem_of_results_pair {E A} : ElemOf (() * A) (t () E A) :=
  λ x e, x ∈ (e ()).(results).
#[global] Typeclasses Opaque elem_of_results.

#[global] Instance elem_of_result {E A} : ElemOf (result E A) (t () E A) :=
  λ x e, match x with
         | Ok v => v ∈ e
         | Error err => err ∈ (map snd (e ()).(errors))
         end.
#[global] Typeclasses Opaque elem_of_result.

(** Takes an option but convert None into an error *)
Definition error_none {St E A} (e : E) : option A -> t St E A :=
  from_option mret (mthrow e).

(** Takes an option but convert None into a discard *)
Definition discard_none {St E A} : option A -> t St E A :=
  from_option mret mdiscard.

(** Maps the error to another error type. *)
Definition map_error {St E E' A} (f : E -> E') (e : t St E A) : t St E' A :=
  λ st, make (e st).(results) (map (λ '(st', r), (st', f r)) (e st).(errors)).
(** Merge the results of two executions *)

(** * Unfold typeclass for results *)

Class UnfoldElemOf {A E} (x : A) (e : t () E A) (Q : Prop) :=
  {unfold_elem_of : x ∈ e ↔ Q}.
#[global] Hint Mode UnfoldElemOf + + - + - : typeclass_instances.

#[global] Instance unfold_elem_of_default {A E} (x : A) (e : t () E A) :
  UnfoldElemOf x e (x ∈ e) | 1000.
Proof. done. Qed.

#[export] Hint Extern 5 (UnfoldElemOf ?x (match ?b with _ => _ end) ?G) =>
  has_option SetUnfoldMatch;
  let H := fresh in
  match G with
  | ?Q => is_evar Q; unshelve eassert (UnfoldElemOf x _ _) as H
  | ?Q ?y => is_evar Q; unshelve eassert (UnfoldElemOf x _ (_ y)) as H
  | ?Q ?x ?y => is_evar Q; unshelve eassert (UnfoldElemOf x _ (_ x y)) as H
  | ?Q ?x ?y ?z => is_evar Q; unshelve eassert (UnfoldElemOf x _ (_ x y z)) as H
  end;
  [.. | apply H];
  [intros; destruct b; shelve | ..];
  destruct b; cbn zeta match : typeclass_instances.

#[global] Instance UnfoldElemOf_proper {A E} :
  Proper (@eq A ==> @eq (t () E A) ==> iff ==> iff) UnfoldElemOf.
Proof. solve_proper2_tc. Qed.

(** Enables Exec unfolding in regular set_unfold *)
Class Unfold := unfold {}.

#[global] Instance UnfoldElemOfSetUnfoldElemOf `{UnfoldElemOf E A x e P} `{Unfold} :
  SetUnfoldElemOf x e P.
Proof. tcclean. apply unfold_elem_of. Qed.

(** Enable that option locally. *)
#[local] Existing Instance unfold.

(** ** Actual unfolding lemmas *)

#[global] Instance unfold_elem_of_make {E A} x l l' P:
  SetUnfoldElemOf x (map snd l) P →
  UnfoldElemOf x ((λ _, make l l') : t () E A) P.
Proof. tcclean. naive_solver. Qed.

#[global] Instance unfold_elem_of_mret {E A} x y:
  UnfoldElemOf x (mret y : t () E A) (x = y).
Proof. tcclean. unfold mret, mret_inst, elem_of, elem_of_results. cbn in *. set_solver. Qed.

#[global] Instance unfold_elem_of_merge {E A} x (e e' : t () E A) P Q:
  UnfoldElemOf x e P →
  UnfoldElemOf x e' Q →
  UnfoldElemOf x (λ _, merge (e ()) (e' ())) (P ∨ Q).
Proof. tcclean. unfold merge, elem_of, elem_of_results. destruct e. destruct e'. set_solver. Qed.

#[global] Instance unfold_elem_of_mbind {E A B} (x : B) (e : t () E A) (f : A → t () E B) P:
  (∀ y, UnfoldElemOf y e (P y)) →
  UnfoldElemOf x (e ≫= f) (∃ y, P y ∧ x ∈ f y) | 20.
Proof.
  tcclean. deintro. intros _.
  unfold mbind, mbind_inst, elem_of, elem_of_results.
  destruct (e ()) as [l es].
  cbn.
  setoid_rewrite unfold_elem_of.
  induction l as [|[[] a ] lr [H H0]].
  1: set_solver.
  do 2 set_unfold.
  split.
  {
    cdestruct |- *** as Hres ## cdestruct_or.
    1: eexists a; unfold elem_of at 2, elem_of_results; set_unfold; split; eexists (_,_); split; last eapply Hres.
    1-3: try reflexivity; now left.
    enough (∃ x0 : A, (∃ x1 : () * A, x0 = x1.2 ∧ x1 ∈ lr) ∧ x ∈ f x0) by naive_solver.
    eapply H.
    eexists (_,_).
    naive_solver.
  }
  {
    cdestruct |- *** as Hres ## cdestruct_or.
    1: eexists (_,_); split; [|left]; cbn; try reflexivity.
    1: unfold elem_of, elem_of_results in * |-; set_unfold in Hres; cbn in *; cdestruct Hres; eauto.
    cdestruct |- ***.
    enough (∃ x0 : A, (∃ x : () * A, x0 = x.2 ∧ x ∈ lr) ∧ x ∈ f x0) by naive_solver.
    eexists _; split; try eassumption; eexists (_,_); naive_solver.
  }
Qed.

#[global] Instance unfold_elem_of_bind_guard `{Decision P} {E A} (e : t () E A)
    (err : E) a Q:
  UnfoldElemOf a e Q →
  UnfoldElemOf a (guard_or err P;; e) (P ∧ Q) | 10.
Proof. tcclean. case_guard; set_solver. Qed.

#[global] Instance unfold_elem_of_bind_guard_discard `{Decision P} {E A} (e : t () E A) a Q:
  UnfoldElemOf a e Q →
  UnfoldElemOf a (guard_discard P;; e) (P ∧ Q) | 10.
Proof. tcclean. case_guard_discard; set_solver. Qed.

#[global] Instance unfold_elem_of_fmap {E A B} (x : B) (e : t () E A) (f : A → B) P:
  (∀ y, UnfoldElemOf y e (P y)) →
  UnfoldElemOf x (f <$> e) (∃ y, P y ∧ x = f y).
Proof. tcclean. unfold elem_of, elem_of_results, fmap, fmap_inst.
 destruct (e ()) as [l es]. cbn. set_unfold. set_solver. Qed.

#[global] Instance unfold_elem_of_mdiscard {E A} (x : A) :
  UnfoldElemOf x (mdiscard : t E A) False.
Proof. tcclean. unfold mdiscard. set_solver. Qed.


(** * Unfold the [has_error] predicate *)

Class UnfoldHasError `(e : t E A) (Q : Prop) :=
  {unfold_has_error : has_error e ↔ Q }.
#[global] Hint Mode UnfoldHasError + + + - : typeclass_instances.

#[global] Instance unfold_has_error_default `(e : t E A) :
  UnfoldHasError e (has_error e) | 1000.
Proof. done. Qed.

#[global] Instance unfold_has_error_mret {E A} (x : A):
  UnfoldHasError (mret x: t E A) False.
Proof. done. Qed.

#[global] Instance unfold_has_error_mthrow {E A} (err : E):
  UnfoldHasError (mthrow err: t E A) True.
Proof. done. Qed.

#[global] Instance unfold_has_error_mdiscard {E A}:
  UnfoldHasError (mdiscard: t E A) False.
Proof. done. Qed.


#[global] Instance unfold_has_error_merge {E A} (e e' : t E A) P Q:
  UnfoldHasError e P →
  UnfoldHasError e' Q →
  UnfoldHasError (merge e e') (P ∨ Q).
Proof.
  tcclean.
  destruct e as [ ? []]; destruct e' as [? []]; cbn in *; naive_solver.
Qed.

#[global] Instance unfold_has_error_mbind {E A B} (e : t E A) (f : A → t E B) P Q R:
  UnfoldHasError e P →
  (∀ y, UnfoldElemOf y e (Q y)) →
  (∀ y, UnfoldHasError (f y) (R y)) →
  UnfoldHasError (e ≫= f) (P ∨ ∃ y, Q y ∧ R y) | 20.
Proof.
  tcclean.
  clear H.
  clear H1.
  clear H0.
  destruct e as [l e]; cbn.
  setoid_rewrite unfold_elem_of.
  induction l.
  - set_solver.
  - cbn. rewrite unfold_has_error. set_solver.
Qed.

#[global] Instance unfold_has_error_bind_guard `{Decision P} {E A} (e : t E A)
  (err : E) Q:
  UnfoldHasError e Q →
  UnfoldHasError (guard_or err P;; e) (¬ P ∨ Q) | 10.
Proof. tcclean. case_guard; try rewrite unfold_has_error; naive_solver. Qed.

#[global] Instance unfold_has_error_bind_guard_discard `{Decision P} {E A} (e : t E A) Q:
  UnfoldHasError e Q →
  UnfoldHasError (guard_discard P;; e) (P ∧ Q) | 10.
Proof. tcclean. case_guard_discard; try rewrite unfold_has_error; naive_solver. Qed.

#[global] Instance unfold_has_error_fmap {E A B} (e : t E A) (f : A → B) P:
  UnfoldHasError e P →
  UnfoldHasError (f <$> e) P.
Proof. tcclean. destruct e as [l es]. cbn. set_solver. Qed.

End Exec.
