(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
(*      Shreeka Lohani, University of Cambridge                               *)
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

Definition lift_res_st `(r : res (St * E) (St * A)) : t St E A :=
  λ st, r.

#[global] Instance elem_of_results {E A} : ElemOf A (res E A) :=
  λ x r, x ∈ r.(results).
#[global] Typeclasses Opaque elem_of_results.

#[global] Instance elem_of_results_no_state {St E A} :
    ElemOf A (res (St * E) (St * A)) :=
  λ x r, x ∈ (map snd r.(results)).
#[global] Typeclasses Opaque elem_of_results_no_state.

Lemma elem_of_results_no_state_intro {St E A}
    (r : res (St * E) (St * A)) st (x : A) :
  Exec.elem_of_results (st, x) r → x ∈ r.
Proof.
  unfold elem_of, elem_of_results, elem_of_results_no_state.
  cbn.
  intro H.
  rewrite elem_of_list_fmap.
  exists (st, x).
  split; [reflexivity|exact H].
Qed.

Lemma elem_of_results_no_state_elim {St E A}
    (r : res (St * E) (St * A)) (x : A) :
  x ∈ r → ∃ st, Exec.elem_of_results (st, x) r.
Proof.
  unfold elem_of, elem_of_results, elem_of_results_no_state.
  cbn.
  rewrite elem_of_list_fmap.
  intros [[st x'] [Heq H]].
  inversion Heq; subst.
  exists st.
  exact H.
Qed.


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

#[global] Instance unfold_elem_of_mcallM_MState_get {St E} st (x : St * St) :
  UnfoldElemOf x
    (@mcallM (MState St) (MState_ret St) (Exec.t St E)
       (@st_call_MState St E) MGet st) (x = (st, st)).
Proof.
  tcclean.
  unfold mcallM, st_call_MState.
  set_solver.
Qed.

#[global] Instance unfold_elem_of_mcallM_MState_set {St E}
    st st' (x : St * unit) :
  UnfoldElemOf x
    (@mcallM (MState St) (MState_ret St) (Exec.t St E)
       (@st_call_MState St E) (MSet st') st) (x = (st', ())).
Proof.
  tcclean.
  unfold mcallM, st_call_MState.
  set_solver.
Qed.

Lemma elem_of_state_get_bind {St E A} st (x : St * A)
    (k : St → Exec.t St E A) :
  x ∈ (((λ s : St, make [(s, s)] []) ≫= k) st) ↔ x ∈ k st st.
Proof.
  unfold mbind, mbind_inst, res_mbind_inst, merge.
  cbn.
  set_solver.
Qed.

Lemma elem_of_state_set_bind {St E A} st st' (x : St * A)
    (k : unit → Exec.t St E A) :
  x ∈ (((λ _ : St, make [(st', ())] []) ≫= k) st) ↔ x ∈ k () st'.
Proof.
  unfold mbind, mbind_inst, res_mbind_inst, merge.
  cbn.
  set_solver.
Qed.

Lemma elem_of_bind_intro {St E A B} st st' st'' a b
    (e : Exec.t St E A) (k : A → Exec.t St E B) :
  Exec.elem_of_results (st', a) (e st) →
  Exec.elem_of_results (st'', b) (k a st') →
  Exec.elem_of_results (st'', b) ((e ≫= k) st).
Proof.
  unfold elem_of, elem_of_results.
  unfold mbind, mbind_inst, res_mbind_inst, merge.
  destruct (e st) as [l es].
  cbn.
  revert st' a st'' b.
  induction l as [|[st0 a0] l IH]; intros st' a st'' b He Hk.
  - inversion He.
  - cbn in He.
    apply elem_of_cons in He as [He|He].
    + inversion He; subst.
      cbn.
      rewrite elem_of_app.
      left.
      exact Hk.
    + cbn.
      rewrite elem_of_app.
      right.
      eapply IH; eauto.
Qed.

Lemma elem_of_bind_elim {St E A B} st (x : St * B)
    (e : Exec.t St E A) (k : A → Exec.t St E B) :
  Exec.elem_of_results x ((e ≫= k) st) →
  ∃ st' a,
    Exec.elem_of_results (st', a) (e st) ∧
    Exec.elem_of_results x (k a st').
Proof.
  unfold elem_of, elem_of_results.
  unfold mbind, mbind_inst, res_mbind_inst, merge.
  destruct (e st) as [l es].
  cbn.
  induction l as [|[st' a] l IH]; cbn.
  - inversion 1.
  - intro H.
    apply elem_of_app in H as [H|H].
    + exists st', a.
      split; [left; reflexivity|exact H].
    + apply IH in H as [st'' [a' [He Hk]]].
      exists st'', a'.
      split; [right; exact He|exact Hk].
Qed.

Lemma elem_of_fin_enum n (i : fin n) : i ∈ fin_enum n.
Proof.
  induction i; cbn; set_solver.
Qed.

Lemma elem_of_mchoosel {St E A} st (x : A) (l : list A) :
  x ∈ l →
  Exec.elem_of_results (st, x) ((mchoosel l : Exec.t St E A) st).
Proof.
  intro Hx.
  unfold mchoosel.
  unfold elem_of, Exec.elem_of_results.
  cbn.
  set_unfold.
  apply elem_of_list_lookup in Hx as [i Hi].
  assert (Hlt : i < length l) by (eapply lookup_lt_Some; eauto).
  exists st, (nat_to_fin Hlt).
  split.
  - split.
    + change (nat_to_fin Hlt ∈ fin_enum (length l)).
      apply elem_of_fin_enum.
    + reflexivity.
  - f_equal.
    symmetry.
    apply vlookup_lookup.
    rewrite vec_to_list_to_vec.
    rewrite fin_to_nat_to_fin.
    exact Hi.
Qed.

Lemma elem_of_res_bind_intro {E A B} a b
    (e : Exec.res E A) (k : A → Exec.res E B) :
  Exec.elem_of_results a e →
  Exec.elem_of_results b (k a) →
  Exec.elem_of_results b (e ≫= k).
Proof.
  unfold elem_of, elem_of_results.
  unfold mbind, res_mbind_inst, merge.
  destruct e as [l es].
  cbn.
  revert a b.
  induction l as [|a0 l IH]; intros a b He Hk.
  - inversion He.
  - cbn in He.
    apply elem_of_cons in He as [He|He].
    + inversion He; subst.
      cbn.
      rewrite elem_of_app.
      left.
      exact Hk.
    + cbn.
      rewrite elem_of_app.
      right.
      eapply IH; eauto.
Qed.

Lemma elem_of_res_bind_elim {E A B} b
    (e : Exec.res E A) (k : A → Exec.res E B) :
  Exec.elem_of_results b (e ≫= k) →
  ∃ a, Exec.elem_of_results a e ∧ Exec.elem_of_results b (k a).
Proof.
  unfold elem_of, elem_of_results.
  unfold mbind, res_mbind_inst, merge.
  destruct e as [l es].
  cbn.
  induction l as [|a l IH]; cbn.
  - inversion 1.
  - intro H.
    apply elem_of_app in H as [H|H].
    + exists a.
      split; [left; reflexivity|exact H].
    + apply IH in H as [a' [Ha Hk]].
      exists a'.
      split; [right; exact Ha|exact Hk].
Qed.

Lemma elem_of_res_mchoose {E n} (i : fin n) :
  Exec.elem_of_results i (mchoose n : Exec.res E (fin n)).
Proof.
  unfold mchoose.
  unfold elem_of, Exec.elem_of_results.
  cbn.
  apply elem_of_fin_enum.
Qed.

Lemma elem_of_res_mchoosel {E A} (x : A) (l : list A) :
  x ∈ l →
  Exec.elem_of_results x (mchoosel l : Exec.res E A).
Proof.
  intro Hx.
  unfold mchoosel.
  unfold elem_of, Exec.elem_of_results.
  cbn.
  set_unfold.
  apply elem_of_list_lookup in Hx as [i Hi].
  assert (Hlt : i < length l) by (eapply lookup_lt_Some; eauto).
  exists (nat_to_fin Hlt).
  split.
  - symmetry.
    apply vlookup_lookup.
    rewrite vec_to_list_to_vec.
    rewrite fin_to_nat_to_fin.
    exact Hi.
  - apply elem_of_fin_enum.
Qed.

Lemma elem_of_res_mchoosel_inv {E A} (x : A) (l : list A) :
  Exec.elem_of_results x (mchoosel l : Exec.res E A) →
  x ∈ l.
Proof.
  unfold mchoosel.
  unfold elem_of, Exec.elem_of_results.
  cbn.
  set_unfold.
  intros [idx [Hx _]].
  subst x.
  apply elem_of_list_lookup.
  exists (idx : nat).
  pose proof
    (proj1 (vlookup_lookup (list_to_vec l) idx
              (list_to_vec l !!! idx)) eq_refl) as Hlookup.
  rewrite vec_to_list_to_vec in Hlookup.
  exact Hlookup.
Qed.

Lemma elem_of_lift_res {St E A} st (x : A) (r : Exec.res E A) :
  Exec.elem_of_results x r →
  Exec.elem_of_results (st, x) ((mlift r : Exec.t St E A) st).
Proof.
  unfold elem_of, elem_of_results.
  destruct r as [rs es].
  cbn.
  rewrite elem_of_list_fmap.
  intro H.
  exists x.
  split; [reflexivity|exact H].
Qed.

Lemma elem_of_fmap_inv {St E A B} st st' (b : B)
    (e : Exec.t St E A) (f : A → B) :
  Exec.elem_of_results (st', b) ((f <$> e) st) →
  ∃ a,
    b = f a ∧ Exec.elem_of_results (st', a) (e st).
Proof.
  unfold elem_of, elem_of_results.
  unfold fmap, Exec.fmap_inst.
  destruct (e st) as [rs es].
  cbn.
  rewrite elem_of_list_fmap.
  intros [[st0 a] [Heq Hin]].
  inversion Heq; subst.
  exists a.
  split; [reflexivity|exact Hin].
Qed.

Lemma elem_of_lift_res_inv {St E A} st st' (x : A) (r : Exec.res E A) :
  Exec.elem_of_results (st', x) ((mlift r : Exec.t St E A) st) →
  st' = st ∧ Exec.elem_of_results x r.
Proof.
  unfold elem_of, elem_of_results.
  destruct r as [rs es].
  cbn.
  rewrite elem_of_list_fmap.
  intros [y [Heq Hy]].
  inversion Heq; subst.
  naive_solver.
Qed.

Lemma elem_of_lift_res_set_full_inv {St St' E A}
    (setter : St' → St → St) (r : Exec.res (St' * E) (St' * A))
    st st' a :
  Exec.elem_of_results (st', a) ((Exec.lift_res_set_full setter r) st) →
  ∃ st_inner,
    st' = setter st_inner st ∧ Exec.elem_of_results (st_inner, a) r.
Proof.
  unfold Exec.lift_res_set_full, map_state.
  unfold elem_of, Exec.elem_of_results.
  destruct r as [rs es].
  cbn.
  rewrite elem_of_list_fmap.
  intros [[st_inner a0] [Heq Hin]].
  inversion Heq; subst.
  exists st_inner.
  cbn in Hin.
  naive_solver.
Qed.

Lemma elem_of_liftSt_snd_inv {A B E X} a b a' b' x
    (e : Exec.t B E X) :
  Exec.elem_of_results ((a', b'), x)
    ((Exec.liftSt snd e : Exec.t (A * B) E X) (a, b)) →
  a' = a ∧ Exec.elem_of_results (b', x) (e b).
Proof.
  unfold Exec.liftSt, liftSt_full, map_state.
  unfold elem_of, Exec.elem_of_results.
  destruct (e b) as [rs es] eqn:He.
  cbn.
  rewrite elem_of_list_fmap.
  intros [[b0 x0] [Heq Hin]].
  inversion Heq; subst.
  rewrite He in Hin.
  cbn in Hin.
  naive_solver.
Qed.

Lemma elem_of_liftSt {St St' E A} st st' a
    (getter : St → St') `{Setter St St' getter}
    (e : Exec.t St' E A) :
  Exec.elem_of_results (st', a) (e (getter st)) →
  Exec.elem_of_results (setv getter st' st, a) ((Exec.liftSt getter e) st).
Proof.
  unfold Exec.liftSt, liftSt_full, map_state.
  unfold elem_of, Exec.elem_of_results.
  destruct (e (getter st)) as [rs es] eqn:He.
  cbn.
  rewrite elem_of_list_fmap.
  intro Hin.
  exists (st', a).
  split; [reflexivity|].
  cbn in Hin.
  exact Hin.
Qed.

Lemma elem_of_liftSt_inv {St St' E A} st st' a
    (getter : St → St') `{Setter St St' getter}
    (e : Exec.t St' E A) :
  Exec.elem_of_results (st', a) ((Exec.liftSt getter e) st) →
  ∃ st_inner,
    st' = setv getter st_inner st ∧
    Exec.elem_of_results (st_inner, a) (e (getter st)).
Proof.
  unfold Exec.liftSt, liftSt_full, map_state.
  unfold elem_of, Exec.elem_of_results.
  destruct (e (getter st)) as [rs es] eqn:He.
  cbn.
  rewrite elem_of_list_fmap.
  intros [[st_inner a0] [Heq Hin]].
  inversion Heq; subst.
  exists st_inner.
  cbn in Hin.
  naive_solver.
Qed.

Lemma elem_of_mchoose {St E n} st (i : fin n) :
  Exec.elem_of_results (st, i) ((mchoose n : Exec.t St E (fin n)) st).
Proof.
  unfold mchoose.
  unfold elem_of, Exec.elem_of_results.
  cbn.
  rewrite elem_of_list_fmap.
  exists i.
  split; [reflexivity|apply elem_of_fin_enum].
Qed.

Lemma elem_of_mchoose_inv {St E n} st st' (i : fin n) :
  Exec.elem_of_results (st', i) ((mchoose n : Exec.t St E (fin n)) st) →
  st' = st.
Proof.
  unfold mchoose.
  unfold elem_of, Exec.elem_of_results.
  cbn.
  rewrite elem_of_list_fmap.
  intros [i' [Heq _]].
  inversion Heq.
  reflexivity.
Qed.

Lemma elem_of_mchoosel_inv {St E A} st st' (x : A) (l : list A) :
  Exec.elem_of_results (st', x) ((mchoosel l : Exec.t St E A) st) →
  st' = st ∧ x ∈ l.
Proof.
  unfold mchoosel.
  unfold elem_of, Exec.elem_of_results.
  unfold fmap, Exec.fmap_inst.
  cbn.
  rewrite elem_of_list_fmap.
  intros [[st0 idx] [Heq Hidx]].
  inversion Heq; subst st' x.
  rewrite elem_of_list_fmap in Hidx.
  destruct Hidx as [idx' [Heq_idx _]].
  inversion Heq_idx; subst st0 idx'.
  split; [reflexivity|].
  apply elem_of_list_lookup.
  exists (idx : nat).
  pose proof
    (proj1 (vlookup_lookup (list_to_vec l) idx
              (list_to_vec l !!! idx)) eq_refl) as Hlookup.
  rewrite vec_to_list_to_vec in Hlookup.
  exact Hlookup.
Qed.

Lemma elem_of_mGet {St E} st :
  Exec.elem_of_results (st, st) ((mGet : Exec.t St E St) st).
Proof.
  unfold elem_of, Exec.elem_of_results.
  cbn.
  apply elem_of_list_singleton.
  reflexivity.
Qed.

Lemma elem_of_mGet_inv {St E} st st' x :
  Exec.elem_of_results (st', x) ((mGet : Exec.t St E St) st) →
  st' = st ∧ x = st.
Proof.
  unfold elem_of, Exec.elem_of_results.
  cbn.
  intro H.
  apply elem_of_list_singleton in H.
  inversion H; subst.
  naive_solver.
Qed.

Lemma elem_of_mget {St E T} st (proj : St → T) :
  Exec.elem_of_results (st, proj st) ((mget proj : Exec.t St E T) st).
Proof.
  unfold mget.
  unfold elem_of, Exec.elem_of_results.
  cbn.
  apply elem_of_list_singleton.
  reflexivity.
Qed.

Lemma elem_of_mget_inv {St E T} st st' x (proj : St → T) :
  Exec.elem_of_results (st', x) ((mget proj : Exec.t St E T) st) →
  st' = st ∧ x = proj st.
Proof.
  unfold mget.
  unfold elem_of, Exec.elem_of_results.
  cbn.
  intro H.
  apply elem_of_list_singleton in H.
  inversion H; subst.
  naive_solver.
Qed.

Lemma elem_of_mret {St E A} st (x : A) :
  Exec.elem_of_results (st, x) ((mret x : Exec.t St E A) st).
Proof.
  unfold elem_of, Exec.elem_of_results.
  cbn.
  apply elem_of_list_singleton.
  reflexivity.
Qed.

Lemma elem_of_mret_inv {St E A} st st' x (y : A) :
  Exec.elem_of_results (st', x) ((mret y : Exec.t St E A) st) →
  st' = st ∧ x = y.
Proof.
  unfold elem_of, Exec.elem_of_results.
  cbn.
  intro H.
  apply elem_of_list_singleton in H.
  inversion H; subst.
  naive_solver.
Qed.

Lemma elem_of_mapM_state_inv {St E A B} (f : A → Exec.t St E B)
    (l : list A) st st' bs :
  (∀ x st0 st1 b,
      x ∈ l →
      Exec.elem_of_results (st1, b) (f x st0) →
      st1 = st0) →
  Exec.elem_of_results (st', bs) ((mapM f l : Exec.t St E (list B)) st) →
  st' = st.
Proof.
  revert st st' bs.
  induction l as [|x l IH]; intros st st' bs Hpres Hres.
  - cbn in Hres.
    apply elem_of_mret_inv in Hres as [-> _].
    reflexivity.
  - cbn in Hres.
    apply elem_of_bind_elim in Hres as [st1 [b [Hf Hres]]].
    apply elem_of_bind_elim in Hres as [st2 [bs' [Hmap Hret]]].
    apply elem_of_mret_inv in Hret as [-> _].
    transitivity st1.
    + eapply IH; [|exact Hmap].
      intros y st0 st3 b0 Hy.
      apply Hpres.
      apply elem_of_cons; right; exact Hy.
    + apply Hpres with (x := x) (b := b).
      * apply elem_of_cons; left; reflexivity.
      * exact Hf.
Qed.

Lemma elem_of_guard_discard_inv {St E P} `{Decision P} st st' (p : P) :
  Exec.elem_of_results (st', p) ((guard_discard P : Exec.t St E P) st) →
  st' = st.
Proof.
  unfold guard_discard.
  destruct (decide P) as [Hp|Hnp].
  - intro Hin.
    apply elem_of_mret_inv in Hin as [-> _].
    reflexivity.
  - rewrite mdiscard_eq.
    unfold elem_of, Exec.elem_of_results.
    cbn.
    inversion 1.
Qed.

Lemma elem_of_guard_discard {St E P} `{Decision P} st :
  P →
  ∃ p, Exec.elem_of_results (st, p)
    ((guard_discard P : Exec.t St E P) st).
Proof.
  intro p.
  unfold guard_discard.
  destruct (decide P) as [p'|Hnp].
  - exists p'.
    apply elem_of_mret.
  - exfalso.
    exact (Hnp p).
Qed.

Lemma elem_of_guard_or_inv {St E P} `{Decision P} st st' (err : E) (p : P) :
  Exec.elem_of_results (st', p) ((guard_or err P : Exec.t St E P) st) →
  st' = st.
Proof.
  unfold guard_or.
  destruct (decide P) as [Hp|Hnp].
  - intro Hin.
    apply elem_of_mret_inv in Hin as [-> _].
    reflexivity.
  - unfold elem_of, Exec.elem_of_results.
    cbn.
    inversion 1.
Qed.

Lemma elem_of_guard_or {St E P} `{Decision P} st (err : E) :
  P →
  ∃ p, Exec.elem_of_results (st, p)
    ((guard_or err P : Exec.t St E P) st).
Proof.
  intro p.
  unfold guard_or.
  destruct (decide P) as [p'|Hnp].
  - exists p'.
    apply elem_of_mret.
  - exfalso.
    exact (Hnp p).
Qed.

Lemma elem_of_guard_or_prop {St E P} `{Decision P} st st' (err : E)
    (p : P) :
  Exec.elem_of_results (st', p) ((guard_or err P : Exec.t St E P) st) →
  P.
Proof.
  intro Hres.
  exact p.
Qed.

Lemma elem_of_guard_discard_unit_inv {St E P} `{Decision P} st st' :
  Exec.elem_of_results (st', ())
    ((guard_discard' P : Exec.t St E unit) st) →
  st' = st.
Proof.
  unfold guard_discard'.
  intro Hres.
  apply elem_of_bind_elim in Hres as [st0 [p [Hguard Hret]]].
  apply elem_of_guard_discard_inv in Hguard as ->.
  apply elem_of_mret_inv in Hret as [-> _].
  reflexivity.
Qed.

Lemma elem_of_guard_discard_unit_prop {St E P} `{Decision P} st st' :
  Exec.elem_of_results (st', ())
    ((guard_discard' P : Exec.t St E unit) st) →
  P.
Proof.
  unfold guard_discard'.
  intro Hres.
  apply elem_of_bind_elim in Hres as [st0 [p [Hguard Hret]]].
  exact p.
Qed.

Lemma elem_of_guard_discard_unit {St E P} `{Decision P} st :
  P →
  Exec.elem_of_results (st, ())
    ((guard_discard' P : Exec.t St E unit) st).
Proof.
  intro p.
  unfold guard_discard'.
  destruct (elem_of_guard_discard (E:=E) st p) as [p' Hguard].
  eapply elem_of_bind_intro.
  - exact Hguard.
  - apply elem_of_mret.
Qed.

Lemma elem_of_mSetv {St E} st (v : St) :
  Exec.elem_of_results (v, ()) ((mSetv v : Exec.t St E unit) st).
Proof.
  unfold elem_of, Exec.elem_of_results.
  cbn.
  apply elem_of_list_singleton.
  reflexivity.
Qed.

Lemma elem_of_mSetv_inv {St E} st st' (v : St) :
  Exec.elem_of_results (st', ()) ((mSetv v : Exec.t St E unit) st) →
  st' = v.
Proof.
  unfold elem_of, Exec.elem_of_results.
  cbn.
  intro H.
  apply elem_of_list_singleton in H.
  inversion H.
  reflexivity.
Qed.

Lemma elem_of_mSet {St E} st (upd : St → St) :
  Exec.elem_of_results (upd st, ())
    ((mSet upd : Exec.t St E unit) st).
Proof.
  unfold mSet.
  eapply Exec.elem_of_bind_intro with (st' := st) (a := st).
  - apply elem_of_mGet.
  - apply elem_of_mSetv.
Qed.

Lemma elem_of_mSet_inv {St E} st st' (upd : St → St) :
  Exec.elem_of_results (st', ()) ((mSet upd : Exec.t St E unit) st) →
  st' = upd st.
Proof.
  unfold mSet.
  intro Hres.
  apply Exec.elem_of_bind_elim in Hres as [st0 [s [Hget Hset]]].
  apply elem_of_mGet_inv in Hget as [-> ->].
  apply elem_of_mSetv_inv in Hset.
  exact Hset.
Qed.

Lemma elem_of_mset {St E T} st (proj : St → T)
    `{Setter St T proj} (upd : T → T) :
  Exec.elem_of_results (set proj upd st, ())
    ((mset proj upd : Exec.t St E unit) st).
Proof.
  unfold mset, mSet.
  eapply Exec.elem_of_bind_intro with (st' := st) (a := st).
  - unfold elem_of, Exec.elem_of_results.
    cbn.
    apply elem_of_list_singleton.
    reflexivity.
  - apply elem_of_mSetv.
Qed.

Lemma elem_of_mset_inv {St E T} st st' (proj : St → T)
    `{Setter St T proj} (upd : T → T) :
  Exec.elem_of_results (st', ()) ((mset proj upd : Exec.t St E unit) st) →
  st' = set proj upd st.
Proof.
  unfold mset, mSet.
  intro Hres.
  apply Exec.elem_of_bind_elim in Hres as [st0 [s [Hget Hset]]].
  unfold elem_of, Exec.elem_of_results in Hget.
  cbn in Hget.
  apply elem_of_list_singleton in Hget.
  inversion Hget; subst st0 s.
  apply elem_of_mSetv_inv in Hset.
  exact Hset.
Qed.

Lemma elem_of_bind_mthrow {St E A B} st (x : St * B)
    (e : Exec.t St E A) (f : A → E) :
  Exec.elem_of_results x ((e ≫= λ a, mthrow (f a)) st) → False.
Proof.
  unfold mbind, mbind_inst, res_mbind_inst, merge.
  unfold mthrow, throw_inst, res_throw_inst.
  destruct (e st) as [l es].
  cbn.
  revert x.
  induction l as [|[st' a] l IH]; intros x H.
  - inversion H.
  - cbn in H.
    apply IH in H.
    exact H.
Qed.

Lemma elem_of_results_res_bind_mthrow {E A B} (x : B)
    (e : Exec.res E A) (f : A → E) :
  x ∈ Exec.results (e ≫= λ a, mthrow (f a)) → False.
Proof.
  unfold mbind, res_mbind_inst, merge.
  unfold mthrow, res_throw_inst.
  destruct e as [l es].
  cbn.
  revert x.
  induction l as [|a l IH]; intros x H.
  - inversion H.
  - cbn in H.
    apply IH in H.
    exact H.
Qed.

Lemma elem_of_results_res_bind_exec_mthrow {St E A B} (x : St * B)
    (e : Exec.res (St * E) (St * A)) (f : A → E) :
  x ∈ Exec.results (e ≫= λ '(st, a), @throw_inst St E B (f a) st) →
  False.
Proof.
  unfold mbind, res_mbind_inst, merge.
  unfold mthrow, throw_inst, res_throw_inst.
  destruct e as [l es].
  cbn.
  revert x.
  induction l as [|[st a] l IH]; intros x H.
  - inversion H.
  - cbn in H.
    apply IH in H.
    exact H.
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
