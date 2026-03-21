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

(** Unfortunately this development needs to support two kinds of bitvector.
    The module will attempt to provide smooth interoperability between the two *)

From Stdlib Require Import Lia HexString Eqdep_dec.

From stdpp Require Import decidable countable finite vector pretty.
From stdpp.bitvector Require Import bitvector tactics.

Require Import Options.
Require Import CBase.
Require Import CBool.
Require Import CList.


(** Heterogenous equality decision *)
#[export] Instance bv_eqdep_dec : EqDepDecision bv.
Proof using.
  intros ? ? ? a b.
  destruct decide (bv_unsigned a = bv_unsigned b).
  - left. abstract naive_solver use bv_eq.
  - right. abstract (subst; rewrite JMeq_simpl; naive_solver).
Defined.

(** ** Computation-friendly [EqDecision] for [bv]

The stdpp [bv_eq_dec] produces equality proofs that use [bv_wf_pi]
(proof irrelevance for [BvWf]), which is opaque ([Qed]).  Under [vm_compute],
this makes the proof term inside [left] stuck: any dependent match
([eq_rect], [f_equal], …) on the resulting equality cannot reduce.
This cascades through [Msg.eq_dec], [Ev.eq_dec], [Memory.fulfill], and
the entire promising-model execution.

We replace it with a version whose equality proof reduces completely
under [vm_compute], following the same pattern as [vec_countable] in CVec.v. *)

(** Transparent proof irrelevance for [Is_true].
    [Is_true b] is [if b then True else False].
    When [b = true], both proofs are [I]; when [b = false], there are none. *)
Definition Is_true_pi (b : bool) (p1 p2 : Is_true b) : p1 = p2 :=
  match b return ∀ (p1 p2 : Is_true b), p1 = p2 with
  | true => fun p1 p2 => match p1, p2 with I, I => eq_refl end
  | false => fun p1 => match p1 with end
  end p1 p2.

(** Transparent proof irrelevance for [BvWf], using [Is_true_pi]. *)
Definition BvWf_pi_compute (n : N) (z : Z) (p1 p2 : BvWf n z) : p1 = p2 :=
  Is_true_pi _ p1 p2.

(** Normalizes a [BvWf] proof to [I] by matching on the boolean
    [(0 <=? z) && (z <? bv_modulus n)] — which always reduces for
    concrete [n] and [z] — while ignoring the original (possibly
    opaque) proof entirely.  In the [true] branch the proof is
    replaced by [I : True]; the [false] branch is unreachable for
    well-formed bitvectors. *)
Definition BvWf_compute (n : N) (z : Z) (pf : BvWf n z) : BvWf n z :=
  match (0 <=? z)%Z && (z <? bv_modulus n)%Z as b
    return Is_true b → Is_true b
  with
  | true => fun _ => I
  | false => fun pf => pf
  end pf.

(** Normalize a bitvector so its [BvWf] proof is [I].
    For concrete values, [bv_normalize b] computes to [@BV n v I]. *)
Definition bv_normalize {n : N} (b : bv n) : bv n :=
  @BV n (bv_unsigned b) (BvWf_compute n (bv_unsigned b) (bv_is_wf b)).

#[export] Remove Hints bv_eq_dec : typeclass_instances.
#[export] Remove Hints bv_countable : typeclass_instances.
#[export] Remove Hints bv_finite : typeclass_instances.

#[export] Instance bv_eq_dec_compute (n : N) : EqDecision (bv n) :=
  fun a b =>
    match a, b with
    | @BV _ v1 p1, @BV _ v2 p2 =>
      match Z.eq_dec v1 v2 with
      | left H =>
          left (match H in (_ = v) return ∀ p : BvWf n v, @BV n v1 p1 = @BV n v p with
                | eq_refl => fun p2' => f_equal (@BV n v1) (BvWf_pi_compute n v1 p1 p2')
                end p2)
      | right H => right (fun Heq : @BV n v1 p1 = @BV n v2 p2 =>
                            H (f_equal bv_unsigned Heq))
      end
    end.

#[export] Instance bv_countable_compute n : Countable (bv n) :=
  inj_countable bv_unsigned (Z_to_bv_checked n) (Z_to_bv_checked_bv_unsigned n).

(** Reuse enum/proofs from stdpp's [bv_finite]; the [NoDup] and [elem_of]
    proofs are [EqDecision]-independent so they transfer directly. *)
#[export] Instance bv_finite_compute n : Finite (bv n) := {|
  enum := @enum _ _ (@bv_finite n);
  NoDup_enum := @NoDup_enum _ _ (@bv_finite n);
  elem_of_enum := @elem_of_enum _ _ (@bv_finite n)
|}.

(** Pretty instances *)

Instance pretty_bv {n} : Pretty (bv n) :=
  λ b, HexString.of_Z (bv_unsigned b).

Instance pretty_bvn : Pretty bvn :=
  λ b, HexString.of_Z (bvn_unsigned b).

(** Allow better solving of [BvWf] when the size expression has free-variables
    that are irrelevant and can be removed by [cbn] *)
Hint Extern 15 (BvWf _ _) => cbn; solve_BvWf : typeclass_instances.

(** This make lia slower and more powerful. I think it's better with it on *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(** * Computable transport instance

This implements the transport along bitvector size equality in computable way.*)

#[export] Instance ctrans_bv : CTrans bv :=
  λ n m H b,
    (* Implementation is keep the z and do a non-computable transport of the
       proof. This can break things like reflexivity, but people should use
       [bv_eq] *)
    let '(@BV _ z wf) := b in
    let wf' := match H with eq_refl => wf end
    in @BV m z wf'.

#[export] Instance ctrans_bv_simpl : CTransSimpl bv.
Proof. intros ?? []. bv_solve. Qed.
Opaque ctrans_bv.

Lemma bv_unfold_ctrans_bv n m (e : n = m) s w b z:
  BvUnfold n s w b z → BvUnfold m s w (ctrans e b) z.
Proof. tcclean. subst. simp ctrans. Qed.
#[global] Hint Resolve bv_unfold_ctrans_bv : bv_unfold_db.

Lemma ctrans_bv_0 `(H : n = m) : ctrans H (bv_0 n) = bv_0 m.
Proof. bv_solve. Qed.
#[export] Hint Rewrite @ctrans_bv_0 : ctrans bv_simplify.

Lemma ctrans_Z_to_bv `(H : n = m) z : ctrans H (Z_to_bv n z) = Z_to_bv m z.
Proof. bv_solve. Qed.
#[export] Hint Rewrite @ctrans_Z_to_bv : ctrans bv_simplify.

Lemma bv_unsigned_ctrans `(H : n = m) b :
  bv_unsigned (ctrans H b) = bv_unsigned b.
Proof. bv_solve. Qed.
#[export] Hint Rewrite @bv_unsigned_ctrans : ctrans bv_simplify.

Lemma ctrans_bv_extract i `(H : n = m) `(b : bv p) :
  ctrans H (bv_extract i n b) = bv_extract i m b.
Proof. bv_solve. Qed.
#[export] Hint Rewrite @ctrans_bv_extract : ctrans bv_simplify.

Lemma bv_extract_ctrans `(H : n = m) `(b : bv n) i l :
  bv_extract i l (ctrans H b) = bv_extract i l b.
Proof. bv_solve. Qed.
#[export] Hint Rewrite @bv_extract_ctrans : ctrans bv_simplify.

(** * Rewrite databases *)

Lemma bv_wrap_bv_unsigned' {n m} (b : bv m) :
  n = m -> bv_wrap n (bv_unsigned b) = bv_unsigned b.
Proof. intro H. rewrite H. apply bv_wrap_bv_unsigned. Qed.
#[global] Hint Rewrite @bv_wrap_bv_unsigned' using lia : bv_unfolded_arith.

#[global] Hint Rewrite bv_wrap_small
  using unfold bv_modulus in *; lia : bv_unfolded_arith.
#[global] Hint Rewrite Z_to_bv_bv_unsigned : bv_simplify.

Lemma bv_add_Z_bv_unsigned n (b b' : bv n) : (b `+Z` bv_unsigned b' = b + b')%bv.
Proof. bv_solve. Qed.
#[export] Hint Rewrite bv_add_Z_bv_unsigned : bv_simplify.

#[export] Hint Rewrite Z2N.id using bv_solve : bv_simplify.

(** * [bv_solve] improvements *)

(** We redefine bv_solve to end with [lia || f_equal; lia]. This is because on
    some goals where the size is universally quantified, the extra bv_wrap n on
    either size confuse [lia], but on the other hand, if the size is universally
    quantified we are happy to prove the equality without wrapping.*)
Ltac bv_solve ::=
  bv_simplify_arith;
  (* we unfold signed so we just need to saturate unsigned *)
  bv_saturate_unsigned;
  bv_solve_unfold_tac;
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, bv_unsigned in *;
  simpl;
  (lia || f_equal; lia).

(** Simplify all bitvector and Z equations everywhere and not just the goal like
    [bv_simplify]. Aimed for bitblast and bit by bit analysis*)
Ltac bv_simplify' :=
  forall_hyps ltac:(fun H => bv_simplify H); bv_simplify.

(** Simplify all bitvector and Z equations everywhere and not just the
    goal like [bv_simplify_arith]. Aimed for lia and arithmetic analysis*)
Ltac bv_simplify_arith' :=
  forall_hyps ltac:(fun H => bv_simplify_arith H); bv_simplify_arith.

(** Version of bv_solve that also simplifies the hypotheses *)
Ltac bv_solve' :=
  forall_hyps ltac:(fun H => bv_simplify_arith H); bv_solve.


(** * Extra bitvector functions *)


(* This section might be upstreamed to stdpp. *)
(* TODO add bv_solve support for this section *)

(** Divide [m] by [n] and rounds up. The result is the number of block of size
    [n] required to cover [m]

    Undefined if [n] is zero (in practice the result will also be 0) *)
Definition div_round_up (m n : N) := ((m + (n - 1)) / n)%N.

(** Transform a bitvector to bytes of size n. *)
Definition bv_to_bytes (n : N) {m : N} (b : bv m) : list (bv n) :=
  bv_to_little_endian (Z.of_N $ div_round_up m n) n (bv_unsigned b).

Lemma length_bv_to_bytes (n m : N) (b : bv m) :
  length (bv_to_bytes n b) = N.to_nat (div_round_up m n)%N.
Proof. unfold bv_to_bytes. rewrite length_bv_to_little_endian by lia. lia. Qed.

(** Transform a list of bytes of size n to a bitvector of size m.

    If m is larger than n*(length l), the result is zero-extended to m
    If m is smaller than n*(length l), the result is truncated to m *)
Definition bv_of_bytes {n : N} (m : N) (l : list (bv n)) : bv m :=
  little_endian_to_bv n l |> Z_to_bv m.

Definition bv_get_byte (n i : N) {m} (b : bv m) : bv n :=
  bv_extract (i * n) n b.

Lemma bv_to_bytes_bv_get_byte (n i : N) {m} (b : bv m) (byte : bv n) :
  (0 < n)%N →
  (bv_to_bytes n b) !! i = Some byte ↔ (i * n < m)%N ∧ bv_get_byte n i b = byte.
Proof.
  intro N0.
  unfold bv_get_byte.
  unfold bv_to_bytes.
  unfold div_round_up.
  setoid_rewrite bv_to_little_endian_lookup_Some; [|lia].
  split; intros [H H']; subst; (split; [nia | bv_solve]).
Qed.

Lemma bv_of_bytes_bv_to_bytes n `(b : bv m) :
  n ≠ 0%N → bv_of_bytes m (bv_to_bytes n b) = b.
Proof.
  intro H.
  unfold bv_of_bytes, bv_to_bytes.

  (* Convert in a Z problem *)
  apply bv_eq. bv_unfold. rewrite <- bv_wrap_bv_unsigned.
  generalize (bv_unsigned b); clear b; intro b.

  rewrite little_endian_to_bv_to_little_endian; [|lia].
  rewrite <- N2Z.inj_mul.
  fold (bv_modulus (div_round_up m n * n)).
  fold (bv_wrap (div_round_up m n * n) (bv_wrap m b)).
  rewrite bv_wrap_bv_wrap; [| unfold div_round_up; lia].
  by rewrite bv_wrap_idemp.
Qed.

Definition bv_get_bit (i : N) {n : N} (b : bv n) : bool :=
  negb (bv_extract i 1 b =? bv_0 1).

Definition bv_set_bit (i : N) {n : N} (b : bv n) : bv n :=
  bv_or b (Z_to_bv n (bv_modulus i)).

Definition bv_unset_bit (i : N) {n : N} (b : bv n) : bv n :=
  bv_and b (bv_not (Z_to_bv n (bv_modulus i))).

Program Definition bv_1 (n : N) := Z_to_bv n 1.
Program Definition bv_m1 (n : N) := Z_to_bv n (-1).

Definition bv_eqb {n : N} (bv1 bv2 : bv n) : bool := bool_decide (bv1 = bv2).
Definition bv_neqb {n : N} (bv1 bv2 : bv n) : bool := bool_decide (bv1 ≠ bv2).
Definition bv_redand {n : N} (bv : bv n) : bool := bv_eqb bv (bv_m1 n).
Definition bv_redor {n : N} (bv : bv n) : bool := bv_neqb bv (bv_0 n).


Definition bv_nand {n : N} (bv1 bv2 : bv n) : bv n := bv_and bv1 bv2 |> bv_not.
Definition bv_nor {n : N} (bv1 bv2 : bv n) : bv n := bv_or bv1 bv2 |> bv_not.
Definition bv_xnor {n : N} (bv1 bv2 : bv n) : bv n := bv_xor bv1 bv2 |> bv_not.


(** * Extra [bvn] functions *)

Definition BVN (n : N) (val : Z) {wf: BvWf n val} : bvn := BV n val.

Notation bvn_unsigned bv := (bv_unsigned (bvn_val bv)).
Notation bvn_signed bv := (bv_signed (bvn_val bv)).
Notation Z_to_bvn n z := (bv_to_bvn (Z_to_bv n z)).

#[global] Instance bvn_empty : Empty bvn := BVN 0 0.

Definition bvn_eqb (bv1 bv2 : bvn) : bool := bool_decide (bv1 = bv2).
Definition bvn_neqb (bv1 bv2 : bvn) : bool := bool_decide (bv1 ≠ bv2).
Definition bvn_redand (x : bvn) : bool := x |> bvn_val |> bv_redand.
Definition bvn_redor (x : bvn) : bool := x |> bvn_val |> bv_redor.


Definition bvn_succ (x : bvn) : bvn := x |> bvn_val |> bv_succ.
Definition bvn_pred (x : bvn) : bvn := x |> bvn_val |> bv_pred.
Definition bvn_not (x : bvn) : bvn := x |> bvn_val |> bv_not.
Definition bvn_opp (x : bvn) : bvn := x |> bvn_val |> bv_opp.

Lemma bvn_not_type (x : bvn) : bvn_n (bvn_not x) = bvn_n x.
  Proof. naive_solver. Qed.

Definition bvn_extract (s l : N) (x : bvn) : bvn :=
  x |> bvn_val |> bv_extract s l.

Definition bvn_zero_extend (l : N) (x : bvn) : bvn :=
  x |> bvn_val |> bv_zero_extend l.

Definition bvn_sign_extend (l : N) (x : bvn) : bvn :=
  x |> bvn_val |> bv_sign_extend l.

Definition bvn_binop (f : forall {n : N}, bv n -> bv n -> bv n) (x y : bvn)
    : option bvn :=
  match decide (bvn_n x = bvn_n y) with
  | left eq => Some (f (ctrans eq (bvn_val x)) (bvn_val y) : bvn)
  | right _ => None
  end.



Definition bvn_mul := bvn_binop (@bv_mul).
Definition bvn_add := bvn_binop (@bv_add).
Definition bvn_sub := bvn_binop (@bv_sub).
Definition bvn_divu := bvn_binop (@bv_divu).
Definition bvn_modu := bvn_binop (@bv_modu).
Definition bvn_divs := bvn_binop (@bv_divs).
Definition bvn_quots := bvn_binop (@bv_quots).
Definition bvn_mods := bvn_binop (@bv_mods).
Definition bvn_rems := bvn_binop (@bv_rems). (* Yay REMS! *)
Definition bvn_shiftl := bvn_binop (@bv_shiftl).
Definition bvn_shiftr := bvn_binop (@bv_shiftr).
Definition bvn_ashiftr := bvn_binop (@bv_ashiftr).
Definition bvn_and := bvn_binop (@bv_and).
Definition bvn_or := bvn_binop (@bv_or).
Definition bvn_xor := bvn_binop (@bv_xor).

Definition bvn_concat (b1 b2 : bvn) : bvn :=
  bv_concat (bvn_n b1 + bvn_n b2) (bvn_val b1) (bvn_val b2).

#[global] Instance bvn_countable : Countable bvn.
Proof.
  refine (inj_countable (λ bv : bvn, (bvn_n bv, bvn_unsigned bv)) (λ '(n, val), Some (Z_to_bvn n val)) _).
  intros [n bv]. cbn. by rewrite Z_to_bv_bv_unsigned.
Defined.
