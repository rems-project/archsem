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

(** Add a state monad transformer *)

Require Import Options.
Require Import CBase CMonads CDestruct.
Require Import Effects.

Section ST.
  Context {St : Type}.
  Context `{MRet M} `{MBind M} `{MJoin M} `{FMap M}.

  (** * Definitions *)

  Definition stateT (A : Type):= St → M (St * A).

  Definition st_lift {A : Type} (m : M A) : stateT A := λ s, fmap (s,.) m.

  #[global] Instance st_ret : MRet stateT := λ _ a s, mret (s, a).
  #[global] Instance st_bind : MBind stateT := λ _ _ f ma s,
      '(s', a) ← ma s; f a s'.
  #[global] Instance st_join : MJoin stateT := λ _ mma s, '(s', y) ← mma s; y s'.
  #[global] Instance st_fmap : FMap stateT := λ _ _ f ma s,
      (ma s) |$> (λ '(s, a), (s, f a)).

  #[global] Instance st_call_MState : MCall (MState St) stateT | 10 := λ eff,
      match eff with
      | MSet s => λ _, mret (s, ())
      | MGet => λ s, mret (s, s)
      end.

  #[global] Instance st_throw `{MThrow E M}: MThrow E stateT :=
    λ _ x, st_lift (mthrow x).

  (* Specific instances can override this if they want a state modifying effect
  different from MState. *)
  #[global] Instance st_call_inner `{MCall Eff M} : MCall Eff stateT | 100 :=
    λ eff, st_lift (mcall eff).

  (** * Monad laws and properties *)

  Lemma unfold_stateT_bind `(x : stateT A)
    `(f : A → stateT B) s :
    (x ≫= f) s = '(s, xv) ← x s; f xv s.
  Proof. reflexivity. Qed.

  Context {M_monad : Monad M}.

  Instance st_monad : Monad stateT.
  Proof using M_monad.
    split; intros; apply functional_extensionality; intro s;
      unfold mret, st_ret, mbind, st_bind; try pair_let_clean.
    - by rewrite monad_left_id.
    - by rewrite monad_right_id.
    - rewrite monad_assoc.
      f_equal.
      cdestruct |- ***.
  Qed.

  Context {M_monad_fmap : MonadFMap M}.

  Instance fMon_monad_fmap : MonadFMap stateT.
  Proof using M_monad_fmap.
    intros A B f.
    apply functional_extensionality.
    intro x.
    unfold fmap, mbind, mret, st_fmap, st_bind, st_ret.
    apply functional_extensionality.
    intro s.
    rewrite monad_fmap.
    by pair_let_clean.
  Qed.

  Lemma unfold_stateT_mget `(proj : St → T) s :
    mget (M := stateT) proj s = mret (s, proj s).
  Proof using M_monad M_monad_fmap.
    unfold mget, fmap.
    cbn.
    by rewrite fmap_mret.
  Qed.

End ST.
Arguments stateT : clear implicits.

(** Move to a state transformer monad over a different monad *)
Definition st_move {St M M' A} (f : M (St * A)%type → M' (St * A)%type)
    (mx : stateT St M A) : stateT St M' A :=
  λ s, f (mx s).

(** The state monad is just the state transformer over the id monad *)
Notation stateM St := (stateT St idM).
