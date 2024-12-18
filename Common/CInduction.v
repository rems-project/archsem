(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2022                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zonguyan Liu, Aahrus Univeristy                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aahrus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, Univeristy of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, Univeristy of Cambridge                                 *)
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
(*  1. Redistributions of source code must retain the above copyright         *)
(*     notice, this list of conditions and the following disclaimer.          *)
(*                                                                            *)
(*  2. Redistributions in binary form must reproduce the above copyright      *)
(*     notice, this list of conditions and the following disclaimer in the    *)
(*     documentation and/or other materials provided with the distribution.   *)
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

Require Import Program.Tactics.
Require Import Arith.
Require Import CBase.
Require Import Options.

(** This module exists because I got fed up by how the normal induction tactic
    did not work on custom induction principles. This new tactic is named
    "cinduction" and is based on the "CInduction" typeclass. The induction lemma
    used can be either found by typeclass resolution or by specifying it
    explicitly.

    For an integer of type nat, "induction n" and "cinduction n" do the same
    thing up to calling intro a few times.

    But one can also use the lt_wf_cind instance by calling cinduction n using
    lt_wf_cind, to do a strong induction.

    One can register a custom induction principle for any type, including
    propositions using the typeclass. The typeclass does not impose any shape
    between the input value and the induction predicate. If multiple value are
    needed, you can thus just call cinduction on a tuple.

    In order to name the generated hypotheses, one can use "with", for example:
    cinduction n with [>| intros n IH].

    There is currently no way to use intro patterns in the same way as the
    normal induction. *)

From stdpp Require Export fin_maps.
From stdpp Require Export sets.


Class CInduction {A : Type} (a : A) (P : Prop) :=
  {
    induction_requirement : Prop;
    induction_lemma : induction_requirement -> P
  }.

Arguments induction_lemma {_} _ {_ _}.
Arguments induction_requirement {_} _ {_ _}.

(*** Tactic definition ***)

Ltac instanciate_as_found e :=
  let x :=  fresh in
  let H  := fresh in
  pose (x := e);
  assert (x = e) as H; [reflexivity |];
  rewrite <- H; rewrite -> H;
  clear H; clear x.

(* If someone ever needs to have more than 3 parameter in the induction
   predicate, feel free to add case

   If someone finds a Ltac hack to have exactly the same semantics for any
   number of arguments, Please replace and check that everything depending still
   builds *)
(* TODO make it recursive *)
Ltac pattern_for H :=
  lazymatch (type of H) with
  | _ ?a ?b ?c =>
      try(instanciate_as_found a);
      try(instanciate_as_found b);
      try(instanciate_as_found c);
      pattern a, b, c;
      apply H
  | _ ?a ?b =>
      try(instanciate_as_found a);
      try(instanciate_as_found b);
      pattern a, b;
      apply H
  | _ ?a =>
      try(instanciate_as_found a);
      pattern a;
      apply H
  | _ => fail "Not an application"
  end.

Tactic Notation "cinduction" constr(e) "with" tactic(intr)  :=
  let H := fresh "H" in
  eenough (induction_requirement e) as H;
  [ apply (induction_lemma e) in H |
    hnf; repeat split; intr];
  [ repeat (pattern_for H); fail "Couldn't apply induction" | ..];
  cbn in *.

Tactic Notation "cinduction" constr(e) := cinduction e with intros.

Tactic Notation "cinduction" constr(e) "using" constr(i) "with" tactic(intr) :=
  let P := mk_evar Prop in
  let CI := fresh "CI" in
  let _ := match goal with _ => evar (CI:CInduction e P) end in
  only [CI] : rapply i;
  let H := fresh "H" in
  eenough (@induction_requirement _ e _ CI) as H;
  [ apply (induction_lemma e) in H |
    hnf; repeat split; intr];
  [ repeat (pattern_for H); fail "Couldn't apply induction" | ..];
  cbn in *;
  clear CI.


Tactic Notation "cinduction" constr(e) "using" constr(i) :=
  cinduction e using i with intros.


(*** Example implementations ***)

Program Global Instance nat_cind (n : nat) (P : nat -> Prop) : CInduction n (P n) :=
  {|
    induction_requirement := (P 0) /\ (forall n, P n -> P (S n))
  |}.
Next Obligation.
  intros. induction n; hauto.
Defined.

Program Definition lt_wf_cind (n : nat) (P : nat -> Prop) : CInduction n (P n) :=
  {|
    induction_requirement := (forall n, (forall m, m < n -> P m) -> P n)
  |}.
Next Obligation. apply lt_wf_ind. Qed.

Program Global Instance le_cind (n m: nat) (H : n <= m) (P : nat -> Prop) :
  CInduction H (P m) :=
  {|
    induction_requirement := P n /\ (∀ m, n ≤ m → P m → P (S m))
  |}.
Next Obligation. intros. induction H; hauto. Defined.

Program Global Instance list_cind A (l: list A) (P : list A -> Prop) :
  CInduction l (P l) :=
  {|
    induction_requirement := P [] /\ (∀ a t, P t → P (a :: t))
  |}.
Next Obligation. intros. induction l; hauto. Defined.

Program Definition list_rev_cind A (l: list A) (P : list A -> Prop) :
  CInduction l (P l) :=
  {|
    induction_requirement := P [] /\ (∀ a t, P t → P (t ++ [a]))
  |}.
Next Obligation. intros. apply rev_ind; hauto. Qed.
