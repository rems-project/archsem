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

From stdpp Require Import fin vector.

Require Import Options.
Require Import CBase CBool COption CArith CList CMaps CDestruct CSimp CSets.

(** This file contain all standard-library like code for vectors *)

(** * Vector alter *)
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


(** * Vector partial lookup *)
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

(** * Vector heterogenous equality *)

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


(** * Vector transport *)

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

(** * Vector countable

The stdpp instance of [vec_countable] doesn't compute. This is one that does *)

(** Convert a list to a vector a specified length.
    Returns [None] is list is of the wrong length *)
Fixpoint list_to_vec_n {A} n l : option (vec A n) :=
  match n,l with
  | 0%nat, [] => Some [#]
  | S n, x :: tl => vcons x <$> list_to_vec_n n tl
  | _, _ => None
  end.

Lemma list_to_vec_n_vec_to_list {A} n (v : vec A n): list_to_vec_n n v = Some v.
Proof.
  induction v.
  - reflexivity.
  - cbn. rewrite IHv. done.
Qed.

#[export] Remove Hints stdpp.vector.vec_countable : typeclass_instances.
Instance vec_countable `{Countable A} n : Countable (vec A n) :=
  (inj_countable vec_to_list (list_to_vec_n n) (list_to_vec_n_vec_to_list n)).


(** * cprodn *)

Section CProdn.
  Context {A : Type}.
  Fixpoint cprodn `(v: vec (list A) n) : list (vec A n) :=
    match v with
    | [#] => [[#]]
    | hd ::: tl => hd × cprodn tl |$> (λ '(a, b), a ::: b)
    end.

  Import CSimpPairLet.
  Import CSimpPairExists.
  Import CSimpSetUnfoldElemOf.

  (** This specifies the content of cprodn, but not the order. *)
  Lemma cprodn_spec {n} (v : vec (list A) n) (v0 : vec A n) :
    v0 ∈ cprodn v ↔ ∀ idx : fin n, v0 !!! idx ∈ v !!! idx.
  Proof.
    dependent induction v; dependent destruction v0.
    - cbn. sauto q:on.
    - cbn.
      split.
      + csimp.
        cdestruct |- *** as H H' idx.
        rewrite IHv in H'.
        dependent destruction idx; by cbn.
      + intro H.
        csimp.
        repeat eexists.
        * by specialize (H 0%fin).
        * rewrite IHv. intro idx. by specialize (H (FS idx)).
  Qed.
End CProdn.

(** * vmapM *)

Fixpoint vmapM {A B} `{MBind M, MRet M} (f : A → M B) {n} (v : vec A n) :
    M (vec B n) :=
  match v with
  | [#] => mret [#]
  | hd ::: tl =>
      nhd ← f hd;
      ntl ← vmapM f tl;
      mret (nhd ::: ntl)
  end.
