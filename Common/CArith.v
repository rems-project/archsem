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

From Stdlib Require Import ZArith.
From stdpp Require Import numbers fin.
Require Import Options.
Require Import CBase.

(** This file is about arithmetic helpers and tactic. Concerned types are nat, N, Z and fin *)

(** * Decision instances *)
(** Those instances are defined by stdpp on opaque aliases that this development
doesn't use. *)
#[global] Instance lt_dec : RelDecision lt := Nat.lt_dec.
#[global] Instance le_dec : RelDecision le := Nat.le_dec.

(** * Integer lattice

    [n ⊔ n'] means max and [n ⊓ n'] means min *)

#[global] Instance join_nat : Join nat := Nat.max.
#[global] Instance meet_nat : Meet nat := Nat.min.
#[global] Instance join_pos : Join positive := Pos.max.
#[global] Instance meet_pos : Meet positive := Pos.min.
#[global] Instance join_N : Join N := N.max.
#[global] Instance meet_N : Meet N := N.min.
#[global] Instance join_Z : Join Z := Z.max.
#[global] Instance meet_Z : Meet Z := Z.min.


(** * N and nat unfolding typeclasses *)

(** This allows unfolding around [N.to_nat] *)
Class N2NatUnfold (n : N) (p : nat) := {N2nat_unfold : N.to_nat n = p}.
#[global] Hint Mode N2NatUnfold + - : typeclass_instances.

#[global] Instance n2nat_unfold_default (n : N) :
  N2NatUnfold n (N.to_nat n) | 1000.
Proof. done. Qed.

(** This allows unfolding around [N.of_nat] *)
Class Nat2NUnfold (n : nat) (p : N) := {nat2N_unfold : N.of_nat n = p}.
#[global] Hint Mode Nat2NUnfold + - : typeclass_instances.

#[global] Instance nat2N_unfold_default (n : nat) :
  Nat2NUnfold n (N.of_nat n) | 1000.
Proof. done. Qed.

#[global] Instance n2nat_unfold_nat2n n : N2NatUnfold (N.of_nat n) n.
Proof. tcclean. apply Nat2N.id. Qed.
#[global] Instance nat2n_unfold_n2nat n : Nat2NUnfold (N.to_nat n) n.
Proof. tcclean. apply N2Nat.id. Qed.

#[global] Instance n2nat_unfold_0 : N2NatUnfold 0 0.
Proof. tcclean. apply N2Nat.inj_0. Qed.
#[global] Instance nat2n_unfold_0 : Nat2NUnfold 0 0.
Proof. tcclean. lia. Qed.

#[global] Instance n2nat_unfold_succ n p :
  N2NatUnfold n p → N2NatUnfold (N.succ n) (S p).
Proof. tcclean. apply N2Nat.inj_succ. Qed.
#[global] Instance nat2n_unfold_succ n p :
  Nat2NUnfold n p → Nat2NUnfold (S n) (N.succ p).
Proof. tcclean. apply Nat2N.inj_succ. Qed.

#[global] Instance n2nat_unfold_pred n p :
  N2NatUnfold n p → N2NatUnfold (N.pred n) (pred p).
Proof. tcclean. apply N2Nat.inj_pred. Qed.
#[global] Instance nat2n_unfold_pred n p :
  Nat2NUnfold n p → Nat2NUnfold (pred n) (N.pred p).
Proof. tcclean. apply Nat2N.inj_pred. Qed.

#[global] Instance n2nat_unfold_div2 n p :
  N2NatUnfold n p → N2NatUnfold (N.div2 n) (Nat.div2 p).
Proof. tcclean. apply N2Nat.inj_div2. Qed.
#[global] Instance nat2n_unfold_div2 n p :
  Nat2NUnfold n p → Nat2NUnfold (Nat.div2 n) (N.div2 p).
Proof. tcclean. apply Nat2N.inj_div2. Qed.

#[global] Instance n2nat_unfold_double n p :
  N2NatUnfold n p → N2NatUnfold (N.double n) (2 * p).
Proof. tcclean. apply N2Nat.inj_double. Qed.
#[global] Instance n2nat_unfold_succ_double n p :
  N2NatUnfold n p → N2NatUnfold (N.succ_double n) (S (2 * p)).
Proof. tcclean. apply N2Nat.inj_succ_double. Qed.

#[global] Instance n2nat_unfold_add n n' p p' :
  N2NatUnfold n p → N2NatUnfold n' p' → N2NatUnfold (n + n') (p + p').
Proof. tcclean. apply N2Nat.inj_add. Qed.
#[global] Instance nat2n_unfold_add n n' p p' :
  Nat2NUnfold n p → Nat2NUnfold n' p' → Nat2NUnfold (n + n') (p + p').
Proof. tcclean. apply Nat2N.inj_add. Qed.

#[global] Instance n2nat_unfold_sub n n' p p' :
  N2NatUnfold n p → N2NatUnfold n' p' → N2NatUnfold (n - n') (p - p').
Proof. tcclean. apply N2Nat.inj_sub. Qed.
#[global] Instance nat2n_unfold_sub n n' p p' :
  Nat2NUnfold n p → Nat2NUnfold n' p' → Nat2NUnfold (n - n') (p - p').
Proof. tcclean. apply Nat2N.inj_sub. Qed.

#[global] Instance n2nat_unfold_mul n n' p p' :
  N2NatUnfold n p → N2NatUnfold n' p' → N2NatUnfold (n * n') (p * p').
Proof. tcclean. apply N2Nat.inj_mul. Qed.
#[global] Instance nat2n_unfold_mul n n' p p' :
  Nat2NUnfold n p → Nat2NUnfold n' p' → Nat2NUnfold (n * n') (p * p').
Proof. tcclean. apply Nat2N.inj_mul. Qed.

#[global] Instance n2nat_unfold_pow n n' p p' :
  N2NatUnfold n p → N2NatUnfold n' p' → N2NatUnfold (n ^ n') (p ^ p').
Proof. tcclean. apply N2Nat.inj_pow. Qed.
#[global] Instance nat2n_unfold_pow n n' p p' :
  Nat2NUnfold n p → Nat2NUnfold n' p' → Nat2NUnfold (n ^ n') (p ^ p').
Proof. tcclean. apply Nat2N.inj_pow. Qed.

#[global] Instance n2nat_unfold_max n n' p p' :
  N2NatUnfold n p → N2NatUnfold n' p' → N2NatUnfold (n `max` n') (p `max` p').
Proof. tcclean. apply N2Nat.inj_max. Qed.
#[global] Instance nat2n_unfold_max n n' p p' :
  Nat2NUnfold n p → Nat2NUnfold n' p' → Nat2NUnfold (n `max` n') (p `max` p').
Proof. tcclean. apply Nat2N.inj_max. Qed.

#[global] Instance n2nat_unfold_min n n' p p' :
  N2NatUnfold n p → N2NatUnfold n' p' → N2NatUnfold (n `min` n') (p `min` p').
Proof. tcclean. apply N2Nat.inj_min. Qed.
#[global] Instance nat2n_unfold_min n n' p p' :
  Nat2NUnfold n p → Nat2NUnfold n' p' → Nat2NUnfold (n `min` n') (p `min` p').
Proof. tcclean. apply Nat2N.inj_min. Qed.

#[global] Instance n2nat_unfold_div n n' p p' :
  N2NatUnfold n p → N2NatUnfold n' p' → N2NatUnfold (n `div` n') (p `div` p').
Proof. tcclean. apply N2Nat.inj_div. Qed.
#[global] Instance nat2n_unfold_div n n' p p' :
  Nat2NUnfold n p → Nat2NUnfold n' p' → Nat2NUnfold (n `div` n') (p `div` p').
Proof. tcclean. apply Nat2N.inj_div. Qed.

#[global] Instance n2nat_unfold_mod n n' p p' :
  N2NatUnfold n p → N2NatUnfold n' p' → N2NatUnfold (n `mod` n') (p `mod` p').
Proof. tcclean. apply N2Nat.inj_mod. Qed.
#[global] Instance nat2n_unfold_mod n n' p p' :
  Nat2NUnfold n p → Nat2NUnfold n' p' → Nat2NUnfold (n `mod` n') (p `mod` p').
Proof. tcclean. apply Nat2N.inj_mod. Qed.



(** * fin utils *)

Definition fin0_magic {A} : fin 0 → A :=
  λ 'f, match f with end.


(** * FinUnfold

    Unfolding typeclass along the [fin_to_nat] coercion
 *)

Class FinUnfold (n : nat) (p : fin n) (q : nat) := {fin_unfold : p =@{nat} q}.
Global Hint Mode FinUnfold + + - : typeclass_instances.

Global Instance fin_unfold_default (n : nat) (p : fin n) :
  FinUnfold n p p | 1000.
Proof. done. Qed.

Global Instance fin_unfold_zero (n : nat) :
  FinUnfold (S n) 0 0.
Proof. done. Qed.

Global Instance fin_unfold_FS (n : nat) p q :
  FinUnfold n p q -> FinUnfold (S n) (FS p) (S q).
Proof. tcclean. done. Qed.

Lemma fin_cast_eq_refl {n : nat} (p : fin n) : Fin.cast p eq_refl = p.
Proof. induction p; sfirstorder. Qed.

Lemma fin_to_nat_cast {n m : nat} (p : fin n) (H : n = m) : Fin.cast p H =@{nat} p.
Proof.
  rewrite <- H.
  rewrite fin_cast_eq_refl.
  reflexivity.
Qed.

Global Instance fin_unfold_cast (n m : nat) (H : n = m) p q :
  FinUnfold n p q -> FinUnfold m (Fin.cast p H) q.
Proof. tcclean. by apply fin_to_nat_cast. Qed.

Lemma fin_to_nat_Fin_to_nat {n : nat} (p : fin n) :
  proj1_sig (Fin.to_nat p) =@{nat} p.
Proof. induction p; hauto lq:on. Qed.

Global Instance fin_unfold_L (n m : nat) p q :
  FinUnfold n p q -> FinUnfold (n + m) (Fin.L m p) q.
Proof.
  tcclean.
  setoid_rewrite <- fin_to_nat_Fin_to_nat.
  apply Fin.L_sanity.
Qed.

Global Instance fin_unfold_R (n m : nat) p q :
  FinUnfold n p q -> FinUnfold (m + n) (Fin.R m p) (m + q).
Proof.
  tcclean.
  setoid_rewrite <- fin_to_nat_Fin_to_nat.
  apply Fin.R_sanity.
Qed.

Global Instance fin_unfold_nat_to_fin (n p : nat) (H : (p < n)%nat) :
  FinUnfold n (nat_to_fin H) p.
Proof. tcclean. by rewrite fin_to_nat_to_fin. Qed.

(** Injects a [fin n] into [fin (S n)] *)
Program Definition fin_L1 {n : nat} (p : fin n) : fin (S n) :=
  Fin.cast (Fin.L 1 p) _.
Solve All Obligations with lia.

Global Instance fin_unfold_L1 (n : nat) p q :
  FinUnfold n p q -> FinUnfold (S n) (fin_L1 p) q.
Proof.
  tcclean.
  unfold fin_L1.
  by rewrite fin_unfold.
Qed.
Opaque fin_L1.

Lemma FS_fin_L1 {n : nat} (p : fin n) : FS (fin_L1 p) = fin_L1 (FS p).
Proof.
  apply (inj fin_to_nat).
  by setoid_rewrite fin_unfold.
Qed.

(** For a natural [n], gives the value [n] in [fin (S n)] which is the last
    value *)
Definition fin_last (n : nat) : fin (S n) :=
  nat_to_fin (Nat.lt_succ_diag_r n).

Global Instance fin_unfold_last (n : nat) :
  FinUnfold (S n) (fin_last n) n.
Proof.
  tcclean.
  unfold fin_last.
  by rewrite fin_unfold.
Qed.
Opaque fin_last.

Lemma FS_fin_last (n : nat) : FS (fin_last n) = fin_last (S n).
Proof.
  apply (inj fin_to_nat).
  by setoid_rewrite fin_unfold.
Qed.

Definition fin_last_inv {n} (P : fin (S n) → Type)
  (Hend : P (fin_last n)) (HS : ∀ (i : fin n), P (fin_L1 i)) (i : fin (S n)) : P i.
Proof.
  induction n.
  - inv_fin i.
    + apply Hend.
    + intro i2. inv_fin i2.
  - inv_fin i.
    + pose (H := HS 0%fin).
      apply H.
    + apply IHn.
      * rewrite FS_fin_last.
        apply Hend.
      * intro i.
        rewrite FS_fin_L1.
        apply HS.
Defined.

Program Definition fin_upcast {n m : nat} (H : (n <= m)%nat) (p : fin n) : fin m :=
  nat_to_fin (_ : (p < m) %nat).
Next Obligation.
  intros.
  use (fin_to_nat_lt p).
  lia.
Qed.

Global Instance fin_unfold_fin_upcast (n p : nat) (H : (p <= n)%nat) (i : fin p) q :
  FinUnfold p i q ->
  FinUnfold n (fin_upcast H i) q.
Proof.
  tcclean.
  unfold fin_upcast.
  rewrite fin_unfold.
  reflexivity.
Qed.
Opaque fin_upcast.

(** * Arithemetic simplification *)

Ltac simpl_arith :=
  try setoid_rewrite fin_unfold;
  try setoid_rewrite N2nat_unfold;
  try setoid_rewrite nat2N_unfold.
