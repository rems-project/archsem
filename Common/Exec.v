(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
(*      Zongyuan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
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

    This monad supports states, non determinism, and errors.
    As an intermediate step the [res] monad is defined,
    that supports non-determinism and errors.
    The definition of the execution monad then makes use of [res] and its
    monadic functions, and adds states to both valid results and errors *)

Require Import Options.
Require Import Common.
Require Import Effects.


(* TODO: Make it a top level name *)
Module Exec.

(** * Base execution result definitions *)
Record res {E A : Type} := make {
    results: list A;
    errors: list E;
  }.
Arguments res : clear implicits.
Arguments make {_ _}.

(** Decide if a result has errors *)
Definition has_error `(e : res E A) :=
  match e with
  | make _ [] => False
  | _ => True
  end.
#[global] Instance has_error_dec `(e : res E A): Decision (has_error e).
Proof. unfold_decide. Qed.

(** Merge two execution results by merging successes and errors separately.
    This does not perform de-duplication *)
Definition merge {E A} (er1 er2 : res E A) :=
  make (er1.(results) ++ er2.(results)) (er1.(errors) ++ er2.(errors)).
#[export] Typeclasses Opaque merge.
Arguments merge : simpl never.

(** Create a res record from a set of results, e.g. to convert from pure
    non-determinism to res *)
Definition res_Results {E A C} `{Elements A C} (s : C) : res E A :=
  make (elements s) [].

(** Monadic definitions for executions results *)

#[global] Instance res_mret_inst {E} : MRet (res E) := λ _ v, make [v] [].

#[global] Instance res_mbind_inst {E} : MBind (res E) :=
  λ _ _ f e,
    foldr merge (make [] e.(errors)) (map f e.(results)).
#[global] Typeclasses Opaque res_mbind_inst.

#[global] Instance res_fmap_inst {E} : FMap (res E) :=
  λ _ _ f e, make (map f e.(results)) e.(errors).
#[global] Typeclasses Opaque res_fmap_inst.

#[global] Instance res_throw_inst {E} : MThrow E (res E) :=
  λ _ e, make [] [e].

#[global] Instance res_choose_inst {E} : MChoose (res E) :=
  λ '(ChooseFin n), @res_Results  _ (Fin.t n) _ _ (enum (fin n)).

#[global] Instance result_lift_res {E} : MLift (result E) (res E) := λ A, unpack_result.

(** Convert an execution result into a list of results *)
Definition to_result_list `(e : res E A) : list (result E A) :=
  map Ok e.(results) ++ map Error e.(errors).

(** Convert an execution result with states into a list of results *)
Definition to_stateful_result_list `(e : res (St * E) (St * A)) :
    list (St * result E A) :=
  map (λ '(st,r), (st, Ok r)) e.(results) ++ map (λ '(st,err), (st, Error err))
      e.(errors).

(** Convert an execution result into a list of result states *)
Definition to_state_result_list `(e : res (St * E) (St * A)) :
    list (result St St) :=
  map (Ok ∘ fst) e.(results) ++ map (Error ∘ fst) e.(errors).

(** Convert and execution result into a list of successful states *)
Definition success_state_list `(e : res (St * E) (St * A)) : list St :=
  e.(results).*1.

(** * Base execution monad definitions *)

Definition t {St E A} := St → res (St * E) (St * A).
Arguments t : clear implicits.
#[export] Typeclasses Transparent t.

(** Create an execution from a set of results, e.g. to convert from pure
    non-determinism to Exec *)
Definition Results {St E A C} `{Elements A C} (s : C) : t St E A :=
  λ st, (st,.) <$> res_Results s.

(** Monadic definition based on the respective instances for execution results *)

#[global] Instance mret_inst {St E} : MRet (t St E) := λ _ v st, mret (st,v).

#[global] Instance mbind_inst {St E} : MBind (t St E) :=
  λ _ _ f e st, '(st', a) ← e st; f a st'.
#[global] Typeclasses Opaque mbind_inst.

#[global] Instance fmap_inst {St E} : FMap (t St E) :=
  λ _ _ f e st, (λ '(st',a), (st', f a)) <$> e st.
#[global] Typeclasses Opaque fmap_inst.

#[global] Instance throw_inst {St E} : MThrow E (t St E) :=
  λ _ e st, mthrow (st,e).

#[global] Instance choose_inst {St E} : MChoose (t St E) :=
  λ '(ChooseFin n), @Results _ _ (Fin.t n) _ _ (enum (fin n)).

#[global] Typeclasses Opaque choose_inst.

#[global] Instance st_call_MState {St E} : MCall (MState St) (t St E) | 10 :=
  λ eff,
    match eff with
    | MSet s => λ _, make [(s,())] []
    | MGet => λ s, make [(s,s)] []
    end.

#[global] Instance res_lift_t {St E} : MLift (res E) (t St E) := λ A r st,
    make (map (st,.) r.(results)) (map (st,.) r.(errors)).

Lemma mdiscard_eq {St E A} : mdiscard =@{t St E A} (λ st, make [] []).
Proof. reflexivity. Qed.

Definition map_state `(f : St → St') `(r : res (St * E) (St * A)) :
    res (St' * E) (St' * A) :=
  make (map (λ '(st, a), (f st, a)) r.(results))
       (map (λ '(st, a), (f st, a)) r.(errors)).

Definition liftSt_full {St St' E A} (getter : St → St') (setter : St' → St → St)
    (inner : Exec.t St' E A) : Exec.t St E A :=
  λ st, map_state (λ st', setter st' st) (inner (getter st)).

Definition liftSt {St St' E A} (getter : St → St') `{Setter St St' getter}
    (inner : Exec.t St' E A) : Exec.t St E A :=
  liftSt_full getter (@setv _ _ getter _) inner.

Definition lift_res_set_full {St' St} (setter : St' → St → St)
    `(r : res (St' * E) (St' * A)) : t St E A :=
  λ st, map_state (λ st', setter st' st) r.

Definition lift_res_set {St' St} (getter : St → St') `{Setter St St' getter}
    `(r : res (St' * E) (St' * A)) : t St E A :=
  lift_res_set_full (@setv _ _ getter _) r.

#[global] Instance elem_of_results {E A} : ElemOf A (res E A) :=
  λ x r, x ∈ r.(results).
#[global] Typeclasses Opaque elem_of_results.

#[global] Instance elem_of_results_no_state {St E A} :
    ElemOf A (res (St * E) (St * A)) :=
  λ x r, x ∈ (map snd r.(results)).
#[global] Typeclasses Opaque elem_of_results_no_state.


#[global] Instance elem_of_result {E A} : ElemOf (result E A) (res E A) :=
  λ x e, match x with
         | Ok v => v ∈ e
         | Error err => err ∈ e.(errors)
         end.
#[global] Typeclasses Opaque elem_of_result.

#[global] Instance elem_of_result_no_state {St E A} :
    ElemOf (result E A) (res (St * E) (St * A)) :=
  λ x e, match x with
         | Ok v => v ∈ e
         | Error err => err ∈ (snd <$> e.(errors))
         end.
#[global] Typeclasses Opaque elem_of_result.

(** Takes an option but convert None into a discard *)
Definition discard_none {St E A} : option A -> t St E A :=
  from_option mret mdiscard.

(** Maps the error to another error type. *)
Definition map_error {St E E' A} (f : E -> E') (e : t St E A) : t St E' A :=
  λ st, let est := e st in
    make est.(results) (map (λ '(st', r), (st', f r)) est.(errors)).

(** * Unfold typeclass for execution results *)

Class UnfoldElemOf {A E} (x : A) (e : res E A) (Q : Prop) :=
  {unfold_elem_of : x ∈ e ↔ Q}.
#[global] Hint Mode UnfoldElemOf + + - + - : typeclass_instances.

#[global] Instance unfold_elem_of_default {A E} (x : A) (r : res E A) :
  UnfoldElemOf x r (x ∈ r) | 1000.
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
  Proper (@eq A ==> @eq (res E A) ==> iff ==> iff) UnfoldElemOf.
Proof. solve_proper2_tc. Qed.

(** Enables Exec unfolding in regular set_unfold *)
Class Unfold := unfold {}.

#[global] Instance UnfoldElemOfSetUnfoldElemOf `{UnfoldElemOf E A x e P} `{Unfold} :
  SetUnfoldElemOf x e P.
Proof. tcclean. apply unfold_elem_of. Qed.

(** Enable that option locally. *)
#[local] Existing Instance unfold.

(** ** Actual unfolding lemmas *)

#[global] Instance unfold_elem_of_results {E A} x (e : res E A) P:
  UnfoldElemOf x e P →
  SetUnfoldElemOf x e.(results) P | 1000.
Proof. tcclean. naive_solver. Qed.

#[global] Instance unfold_elem_of_make {E A} x l l' P:
  SetUnfoldElemOf x l P →
  UnfoldElemOf x (make l l' : res E A) P.
Proof. tcclean. naive_solver. Qed.

#[global] Instance unfold_elem_of_mret {St E A} st x y:
  UnfoldElemOf x ((mret y : t St E A) st) (x = (st, y)).
Proof. tcclean. do 2 unfold mret, mret_inst, res_mret_inst. set_solver. Qed.

#[global] Instance unfold_elem_of_merge {E A} x (e e' : res E A) P Q :
  UnfoldElemOf x e P →
  UnfoldElemOf x e' Q →
  UnfoldElemOf x (merge e e') (P ∨ Q).
Proof. tcclean. unfold merge. destruct e. destruct e'. set_solver. Qed.

#[global] Instance unfold_elem_of_mbind {St E A B} st (x : St * B) (e : t St E A)
    (f : A → t St E B) P :
  (∀ y, UnfoldElemOf y (e st) (P y)) →
  UnfoldElemOf x ((e ≫= f) st) (∃ st' y, P (st', y) ∧ x ∈ f y st') | 20.
Proof.
  tcclean. deintro. intros _.
  unfold mbind, mbind_inst.
  destruct (e st) as [l es].
  elim l; cdestruct |- ***; set_solver.
Qed.

#[global] Instance unfold_elem_of_bind_guard `{Decision P} {St E A} st
    (e : t St E A) (err : E) a Q :
  UnfoldElemOf a (e st) Q →
  UnfoldElemOf a ((guard_or err P;; e) st) (P ∧ Q) | 10.
Proof. tcclean. case_guard; set_solver. Qed.

#[global] Instance unfold_elem_of_bind_guard_discard `{Decision P} {St E A} st
    (e : t St E A) a Q :
  UnfoldElemOf a (e st) Q →
  UnfoldElemOf a ((guard_discard P;; e) st) (P ∧ Q) | 10.
Proof. tcclean. case_guard_discard; set_solver. Qed.

#[global] Instance unfold_elem_of_fmap {St E A B} st (x : St * B) (e : t St E A)
    (f : A → B) P :
  (∀ p, UnfoldElemOf p (e st) (P p)) →
  UnfoldElemOf x ((f <$> e) st) (∃ st' y, P (st', y) ∧ x = (st', f y)).
Proof. tcclean. unfold elem_of, elem_of_results, fmap, fmap_inst.
  destruct (e st) as [l es]. cbn. set_unfold.
  cdestruct |- *** #CDestrSplitGoal; repeat eexists; eauto; naive_solver.
Qed.

#[global] Instance unfold_elem_of_mdiscard {St E A} st (x : St * A) :
  UnfoldElemOf x ((mdiscard : t St E A) st) False.
Proof. tcclean. unfold mdiscard, fmap, fmap_inst; cbn. set_solver. Qed.

#[global] Instance unfold_elem_of_Results {St E A C} `{Elements A C} (s : C)
    (x : St * A) st P :
  (∀ y : A, SetUnfoldElemOf y (elements s) (P y)) →
  UnfoldElemOf x (Results (E := E) s st) (P x.2 ∧ x.1 = st).
Proof. tcclean. unfold Results, res_Results. destruct x. cbn. set_solver. Qed.

#[global] Instance unfold_elem_of_mcallM_MChoice {St E} st st' (m : MChoice)
    (v : eff_ret m) :
  UnfoldElemOf (st, v) (mcallM (Exec.t St E) m st') (st = st').
Proof.
  tcclean.
  destruct m.
  cbn -[enum] in *.
  unfold mcallM, choose_inst, enum.
  destruct fin_finite.
  set_solver.
Qed.

#[global] Instance res_unfold_elem_of_mbind {E A B} (x :  B) (e : res E A) (f : A → res E B) P:
  (∀ y, UnfoldElemOf y e (P y)) →
  UnfoldElemOf x (e ≫= f) (∃ y, P y ∧ x ∈ f y) | 20.
Proof.
  tcclean. deintro. intros _.
  unfold mbind, res_mbind_inst.
  destruct e as [l es].
  elim l; cdestruct |- ***; set_solver.
Qed.

(** * Unfold the [has_error] predicate *)

Class UnfoldHasError `(e : res E A) (Q : Prop) :=
  {unfold_has_error : has_error e ↔ Q }.
#[global] Hint Mode UnfoldHasError + + + - : typeclass_instances.

#[global] Instance unfold_has_error_default `(e : res E A) :
  UnfoldHasError e (has_error e) | 1000.
Proof. done. Qed.

#[global] Instance unfold_has_error_mret {St E A} st (x : A) :
  UnfoldHasError ((mret x : t St E A) st) False.
Proof. done. Qed.

#[global] Instance unfold_has_error_mthrow {St E A} st (err : E) :
  UnfoldHasError ((mthrow err: t St E A) st) True.
Proof. done. Qed.

#[global] Instance unfold_has_error_mdiscard {St E A} st :
  UnfoldHasError ((mdiscard: t St E A) st) False.
Proof. done. Qed.


#[global] Instance unfold_has_error_merge {E A} (e e' : res E A) P Q :
  UnfoldHasError e P →
  UnfoldHasError e' Q →
  UnfoldHasError (merge e e') (P ∨ Q).
Proof.
  tcclean.
  destruct e as [ ? []]; destruct e' as [? []]; cbn in *; naive_solver.
Qed.

#[global] Instance unfold_has_error_mbind {St E A B} st (e : t St E A)
    (f : A → t St E B) P Q R :
  UnfoldHasError (e st) P →
  (∀ y, UnfoldElemOf y (e st) (Q y)) →
  (∀ y, UnfoldHasError (f y.2 y.1) (R y)) →
  UnfoldHasError ((e ≫= f) st) (P ∨ ∃ y, Q y ∧ R y) | 20.
Proof.
  tcclean.
  clear H.
  clear H1.
  clear H0.
  unfold mbind, mbind_inst.
  destruct (e st) as [l es]; cbn.
  setoid_rewrite unfold_elem_of.
  induction l as [|[]].
  - set_solver.
  - cbn. rewrite unfold_has_error. set_solver.
Qed.

#[global] Instance unfold_has_error_bind_guard `{Decision P} {St E A} st
  (e : t St E A) (err : E) Q :
  UnfoldHasError (e st) Q →
  UnfoldHasError ((guard_or err P;; e) st) (¬ P ∨ Q) | 10.
Proof. tcclean. case_guard; try rewrite unfold_has_error; naive_solver. Qed.

#[global] Instance unfold_has_error_bind_guard_discard `{Decision P} {St E A} st
    (e : t St E A) Q :
  UnfoldHasError (e st) Q →
  UnfoldHasError ((guard_discard P;; e) st) (P ∧ Q) | 10.
Proof. tcclean. case_guard_discard; try rewrite unfold_has_error; naive_solver. Qed.

#[global] Instance unfold_has_error_fmap {St E A B} st (e : t St E A) (f : A → B) P :
  UnfoldHasError (e st) P →
  UnfoldHasError ((f <$> e) st) P.
Proof. tcclean. unfold fmap, fmap_inst. destruct (e st) as [l es]. easy. Qed.

End Exec.

