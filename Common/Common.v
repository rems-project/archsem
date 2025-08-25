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

(** This file is the top level of most the ASCommon library. Most users should
    just Require Import ASCommon.Common.
 *)

From Hammer Require Export Tactics.
Require Import DecidableClass.
From stdpp Require Export strings.
From stdpp Require Export fin.
From stdpp Require Export pretty.
From stdpp Require Export vector.
From stdpp Require Export finite.
From stdpp Require Export relations.
From stdpp Require Export propset.
Require Export Ensembles.

Require Import Options.
Require Export CBase.
Require Export CDestruct.
Require Export CMonads.
Require Export CArith.
Require Export CBool.
Require Export CList.
Require Export COption.
Require Export CResult.
Require Export CBitvector.
Require Export CSets.
Require Export CMaps.
Require Export CInduction.

(** * Utility functions ***)

(** Update a function at a specific value *)
Definition fun_add {A B} `{EqDecision A} (k : A) (v : B) (f : A → B) :=
  λ x, if k =? x then v else f x.

Definition dfun_add `{EqDecision A} `{CTrans A B}  (k : A) (v : B k) (f : ∀ a, B a) :=
  λ x, match decide (k = x) with
       | left e => ctrans e v
       | _ => f x
       end.


(** countable for sigT, copied from prod_countable *)
#[global] Program Instance sigT_countable `{Countable A} (P : A → Type)
  `{EqDecision (sigT P)}
  `{∀ a : A, EqDecision (P a)} `{∀ a : A, Countable (P a)} : Countable (sigT P)
  := {|
    encode xy := prod_encode (encode (xy.T1)) (encode (xy.T2));
    decode p :=
      x ← prod_decode_fst p ≫= decode;
      y ← prod_decode_snd p ≫= decode; Some (existT x y)
  |}.
Next Obligation.
  intros ??????? [x y]. cbn.
  rewrite prod_decode_encode_fst, prod_decode_encode_snd; cbn.
  by repeat (rewrite decode_encode; cbn).
Qed.


(** * Vectors ***)

(** ** Vector alter *)
Section VAlter.
  Context {A : Type}.
  Context {n : nat}.

  Local Instance valter : Alter (fin n) A (vec A n) :=
    λ f k v, vinsert k (f (v !!! k)) v.

  Lemma vlookup_alter (k : fin n) f (v : vec A n) :
    alter f k v !!! k = f (v !!! k).
  Proof using. unfold alter, valter. by rewrite vlookup_insert. Qed.

  Lemma valter_eq (k : fin n) f (v : vec A n) :
    f (v !!! k) = v !!! k → alter f k v = v.
  Proof using.
    unfold alter, valter.
    intros ->.
    apply vlookup_insert_self.
  Qed.

  #[global] Instance Setter_valter (k : fin n) :
    @Setter (vec A n) A (lookup_total k) := λ f, alter f k.

  #[global] Instance Setter_valter_wf (k : fin n) :
    @SetterWf (vec A n) A (lookup_total k) :=
    { set_wf := Setter_valter k;
      set_get := vlookup_alter k;
      set_eq := valter_eq k
    }.
End VAlter.

(* Vector typeclasses work better with apply rather than the simple apply of the
   default Hint Resolve/Instance *)
Global Hint Extern 3 (LookupTotal _ _ (vec _ _)) =>
         apply vector_lookup_total : typeclass_instances.

Global Hint Extern 3 (Insert _ _ (vec _ _)) =>
         unfold Insert; apply vinsert : typeclass_instances.

Global Hint Extern 3 (Alter _ _ (vec _ _)) =>
         apply valter : typeclass_instances.


Create HintDb vec discriminated.

#[global] Hint Rewrite @lookup_fun_to_vec : vec.
#[global] Hint Rewrite @vlookup_map : vec.
#[global] Hint Rewrite @vlookup_zip_with : vec.
#[global] Hint Rewrite @vlookup_insert : vec.
#[global] Hint Rewrite @vlookup_alter : vec.
#[global] Hint Rewrite @vlookup_insert_self : vec.
#[global] Hint Rewrite @valter_eq using done : vec.
#[global] Hint Rewrite @length_vec_to_list : vec.


(** ** Vector partial lookup *)
Section VecLookup.
  Context {T : Type}.
  Context {n : nat}.

  Global Instance vec_lookup_nat : Lookup nat T (vec T n) :=
    fun m v =>
      match decide (m < n) with
      | left H => Some (v !!! nat_to_fin H)
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
      rewrite length_vec_to_list.
      lia.
  Qed.

  Global Instance vec_lookup_nat_unfold m (v : vec T n) r:
    LookupUnfold m v r →
    LookupUnfold m (vec_to_list v) r.
  Proof using. tcclean. apply vec_to_list_lookup. Qed.

  #[global] Instance vec_lookup_nat_eq_some_unfold m (v : vec T n) x:
    EqSomeUnfold (v !! m) x (∃ H : m < n, v !!! (nat_to_fin H) = x).
  Proof.
    tcclean.
    unfold lookup, vec_lookup_nat.
    hauto lq:on use:Fin.of_nat_ext.
  Qed.

  Lemma vec_lookup_nat_in m (v : vec T n) (H : m < n) :
    v !! m = Some (v !!! nat_to_fin H).
  Proof. rewrite eq_some_unfold. naive_solver. Qed.

  Global Instance vec_lookup_N : Lookup N T (vec T n) :=
    fun m v => v !! (N.to_nat m).
End VecLookup.

#[global] Hint Rewrite @vec_lookup_nat_in : vec.

(** ** Vector heterogenous equality *)

Equations vec_eqdep_dec `{EqDecision T} : EqDepDecision (vec T) :=
  vec_eqdep_dec _ _ _ vnil vnil := left _;
  vec_eqdep_dec _ _ _ (vcons _ _) vnil := right _;
  vec_eqdep_dec _ _ _ vnil (vcons _ _) := right _;
  vec_eqdep_dec _ _ H (vcons x v1) (vcons y v2) :=
    dec_if_and (decide (x = y)) (vec_eqdep_dec _ _ (Nat.succ_inj _ _ H) v1 v2).
Solve All Obligations with
  (intros;
   unfold TCFindEq in *;
   simplify_eq /=;
     rewrite JMeq_simpl in *;
   naive_solver).
#[export] Existing Instance vec_eqdep_dec.


(** ** Vector transport *)

Equations ctrans_vec T : CTrans (vec T) :=
  ctrans_vec _ 0 0 _ vnil := vnil;
  ctrans_vec _ (S x) (S y) H (vcons a v) :=
    vcons a (ctrans_vec T x y (eq_add_S H) v).
#[export] Existing Instance ctrans_vec.

Lemma ctrans_vec_vnil `(H : 0 = 0) A : ctrans H vnil =@{vec A 0} vnil.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @ctrans_vec_vnil : ctrans.

Lemma ctrans_vec_vcons `(H : S x = S y) `(a : A) v :
  ctrans H (vcons a v) = vcons a (ctrans (eq_add_S H) v).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @ctrans_vec_vcons : ctrans.

#[export] Instance ctrans_vec_simpl T : CTransSimpl (vec T).
Proof. intros x p v. induction v; simp ctrans; congruence. Qed.


(** * Finite decidable quantifiers ***)

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


(** * Finite number utilities ***)

Global Instance pretty_fin (n : nat) : Pretty (fin n)  :=
  (fun n => pretty (n : nat)).
Global Hint Mode Pretty ! : typeclass_instances.

Definition fin_to_N {n : nat} : fin n → N := N.of_nat ∘ fin_to_nat.
Coercion fin_to_N : fin >-> N.
