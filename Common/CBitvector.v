(** Unfortunately this development needs to support two kinds of bitvector.
    The module will attempt to provide smooth interoperability between the two *)

Require Import Lia.
Require Import stdpp.decidable.
Require Import stdpp.countable.
Require Export stdpp.unstable.bitvector.
Require Export stdpp.unstable.bitvector_tactics.
Require Import CBase.
Require Import Options.
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



(** This make lia slower and more powerful. I think it's better with it on *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(*** BV conv ***)

Lemma symmetry_symmetry {A} (x y : A) (e : x = y) :
  symmetry (symmetry e) = e.
Proof. by destruct e. Qed.
#[global] Hint Rewrite @symmetry_symmetry : core.

Module BVDecidableType.
  Definition U := N.
  Definition eq_dec (x y:U) : {x = y} + {x <> y} := decide_rel (=) x y.
End BVDecidableType.

Module BVEqDep := Eqdep_dec.DecidableEqDep(BVDecidableType).

Definition bv_conv {n m : N} (e : n = m) (b : bv n) : bv m :=
  match e with
  | eq_refl => b
  end.

Lemma bv_conv_simpl {n} (e : n = n) (b : bv n) :
  bv_conv e b = b.
Proof. by rewrite (BVEqDep.UIP_refl n e). Qed.
#[global] Hint Rewrite @bv_conv_simpl : bv_unfold.

Lemma bv_conv_trans {n m p : N} (e : n = m) (e' : m = p) (b : bv n) :
  b |> bv_conv e |> bv_conv e' = b |> bv_conv (eq_trans e e').
Proof. naive_solver. Qed.

Lemma bv_conv_sym {n m : N} (e : n = m) (bn : bv n) (bm : bv m) :
  bn = bv_conv (symmetry e) bm <-> bv_conv e bn = bm.
Proof. naive_solver. Qed.

Global Instance bv_unfold_bv_conv n m (e : n = m) s w b z:
  BvUnfold n s w b z → BvUnfold m s w (bv_conv e b) z.
Proof. tcclean. naive_solver. Qed.


(*** bv rewrite databases ***)

Lemma bv_wrap_bv_unsigned' {n m} (b : bv m) :
  n = m -> bv_wrap n (bv_unsigned b) = bv_unsigned b.
Proof. intro H. rewrite H. apply bv_wrap_bv_unsigned. Qed.
#[global] Hint Rewrite @bv_wrap_bv_unsigned' using lia : bv_unfolded_arith.

#[global] Hint Rewrite bv_wrap_small
  using unfold bv_modulus in *; lia : bv_unfolded_arith.
#[global] Hint Rewrite Z_to_bv_bv_unsigned : bv_simplify.


Lemma transport_Z_to_bv {n m : N} (e : n = m) (z : Z) :
  bv_conv e (Z_to_bv n z) = Z_to_bv m z.
Proof. scongruence. Qed.
#[global] Hint Rewrite @transport_Z_to_bv : bv_simplify.

Lemma transport_bv_unsigned (n m i l : N) (b : bv n) (e : n = m):
  bv_unsigned (bv_conv e b) = bv_unsigned b.
Proof. scongruence. Qed.
#[global] Hint Rewrite transport_bv_unsigned : bv_simplify.

Lemma transport_bv_extract1 (n m i l : N) (b : bv n) (e : n = m):
  bv_extract i l (bv_conv e b) = bv_extract i l b.
Proof. scongruence. Qed.
#[global] Hint Rewrite transport_bv_extract1 : bv_simplify.

Lemma transport_bv_extract2 (n i l l' : N) (b : bv n) (e : l = l'):
  bv_conv e (bv_extract i l b) = bv_extract i l' b.
Proof. scongruence. Qed.
#[global] Hint Rewrite transport_bv_extract2 : bv_simplify.



(*** bv_solve improvements ***)


(* Makes bv_unfold slower but more powerful, we'll see if that is better. *)
Global Hint Constants Transparent : bv_unfold_db.

(** Simplify all bitvector equation in Z equations everywhere. Aimed for
    bitblast and bit by bit analysis*)
Ltac bv_simplify' :=
  forall_hyps ltac:(fun H => bv_simplify H); bv_simplify.

(** Simplify all bitvector equation in Z equations everywhere. Aimed for
    lia and arithmetic analysis*)
Ltac bv_simplify_arith' :=
  forall_hyps ltac:(fun H => bv_simplify_arith H); bv_simplify_arith.

(** Improvement of bv_solve that also simplifies the hypothesis *)
Ltac bv_solve' :=
  forall_hyps ltac:(fun H => bv_simplify_arith H); bv_solve.


(*** Extra bitvector function ***)


(* This section might be upstreamed to stdpp. *)
(* TODO add bv_solve support for this section *)

(** Divide [m] by [n] and rounds up. The result is the number of block of size
    [n] required to cover [m]

    Undefined if [n] is zero (in practice the result will also be 0) *)
Definition div_round_up (m n : N) := ((m + (n - 1)) / n)%N.

(** Transform a bitvector to bytes of size n. *)
Definition bv_to_bytes (n : N) {m : N} (b : bv m) : list (bv n) :=
  bv_to_little_endian (Z.of_N $ div_round_up m n) n (bv_unsigned b).

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
  bv_and b (Z_to_bv n (bv_modulus i)).

Definition bv_unset_bit (i : N) {n : N} (b : bv n) : bv n :=
  bv_or b (bv_not (Z_to_bv n (bv_modulus i))).

Program Definition bv_1 (n : N) := Z_to_bv n 1.
Program Definition bv_m1 (n : N) := Z_to_bv n (-1).

Definition bv_eqb {n : N} (bv1 bv2 : bv n) : bool := bool_decide (bv1 = bv2).
Definition bv_neqb {n : N} (bv1 bv2 : bv n) : bool := bool_decide (bv1 ≠ bv2).
Definition bv_redand {n : N} (bv : bv n) : bool := bv_eqb bv (bv_m1 n).
Definition bv_redor {n : N} (bv : bv n) : bool := bv_neqb bv (bv_0 n).


Definition bv_nand {n : N} (bv1 bv2 : bv n) : bv n := bv_and bv1 bv2 |> bv_not.
Definition bv_nor {n : N} (bv1 bv2 : bv n) : bv n := bv_or bv1 bv2 |> bv_not.
Definition bv_xnor {n : N} (bv1 bv2 : bv n) : bv n := bv_xor bv1 bv2 |> bv_not.


(*** Extra bvn functions ***)

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
  | left eq => Some (f (bv_conv eq (bvn_val x)) (bvn_val y) : bvn)
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
