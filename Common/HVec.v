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

From stdpp Require Export fin.

Require Import Options.
Require Import CBase CArith.


Fixpoint hvec (n : nat) : (fin n -> Type) -> Type :=
  match n with
  | 0%nat => fun _ => unit
  | S m => fun T => ((T 0%fin) * hvec m (T ∘ FS))%type
  end.
Arguments hvec {n} T.

Fixpoint hget {n : nat} (i : fin n) : forall T : fin n -> Type, hvec T -> T i :=
  match i with
  | 0%fin => fun _ v => v.1
  | FS p => fun _ v => hget p _ v.2
  end.
Arguments hget {n} i {T} v.

Fixpoint hvec_func {n : nat} : forall T : fin n -> Type, (forall i, T i) -> hvec T :=
  match n with
  | 0%nat => fun _ f => ()
  | S m => fun _ f => (f 0%fin, hvec_func _ (fun x => f (FS x)))
  end.
Arguments hvec_func {n T} f.

Fixpoint hset {n : nat} (i : fin n) : forall T : fin n -> Type, T i -> hvec T -> hvec T :=
  match i with
  | 0%fin => fun _ nv v => (nv, v.2)
  | FS p => fun _ nv v => (v.1, hset p _ nv v.2)
  end.
Arguments hset {n} i {T} nv v.

Lemma hvec_get_func {n : nat} {T : fin n -> Type} (i : fin n) (f : forall i, T i) :
  hget i (hvec_func f) = f i.
Proof. induction i; hauto. Qed.

Lemma hvec_get_set_same {n : nat} {T : fin n -> Type}
  (v : hvec T) (i : fin n) (nv : T i) :
  hget i (hset i nv v) = nv.
Proof. induction i; hauto. Qed.

Lemma hvec_get_set_diff {n : nat} {T : fin n -> Type}
  (v : hvec T) (i j : fin n) (nv : T j) :
  i ≠ j -> hget i (hset j nv v) = hget i v.
Proof. induction i; sauto dep:on. Qed.

(* Technically, this is mapi, but a plain map can't exist because of dependent
 typing *)
Definition hmap {n : nat} {T1 T2 : fin n -> Type} (f : forall i, T1 i -> T2 i)
  (v : hvec T1) : hvec T2 := hvec_func (fun i => f i (hget i v)).

Definition hmap2 {n : nat} {T1 T2 T3 : fin n -> Type} (f : forall i, T1 i -> T2 i -> T3 i)
  (v1 : hvec T1) (v2 : hvec T2) : hvec T3
  := hvec_func (fun i => f i (hget i v1) (hget i v2)).

Lemma hget_hmap {n : nat} {T1 T2 : fin n -> Type} (f : forall i, T1 i -> T2 i)
  (v : hvec T1) (i : fin n) :
  hget i (hmap f v) = f i (hget i v).
Proof.
  unfold hmap.
  rewrite hvec_get_func.
  reflexivity.
Qed.

Definition hlast {n : nat} {T : fin (S n) -> Type} (v : hvec T) : T (fin_last n)
  := hget (fin_last n) v.
