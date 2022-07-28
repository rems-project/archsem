(** This file is the top level of the SSCCommon library. Users should just
    Require Import SSCCommon.Common.
 *)

From Hammer Require Export Tactics.
From RecordUpdate Require Export RecordSet.
Require Export bbv.Word.
Require Import DecidableClass.
From stdpp Require Export strings.

Require Export CBase.
Require Export CBool.
Require Export CList.

(********** Bitvectors **********)

(* Interface Equality decision for words (from bbv) *)
Global Instance word_eq_dec n : EqDecision (word n).
Proof.
  unfold EqDecision.
  unfold Decision.
  apply weq.
Defined.

(********** Utility functions **********)

(** Update a function at a specific value *)
Definition fun_add {A B} {_: EqDecision A} (k : A) (v : B) (f : A -> B) :=
  fun x : A => if k =? x then v else f x.
