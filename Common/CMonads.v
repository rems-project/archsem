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

(** This module cover all thing related to generic monad reasoning *)

Require Import Options.
Require Import CBase.
Require Import CDestruct.

(** * Generic monad lift

This allows to have a generic monad lifting procedure [mlift]. New instances
should only be added to [MLift]. [MLiftT] is only for the transitive closure.

Care should be taken to not add two different paths between two monads,
otherwise there is a risk of the two different paths being selected in two
different [mlift] terms that will look the same but be silently different.
 *)

Class MLift (M M' : Type → Type) := mlift_in : ∀ A, M A → M' A.
Arguments mlift_in {_ _ _ _}.
Hint Mode MLift - ! : typeclass_instances.
Class MLiftT (M M' : Type → Type) := mlift : ∀ A, M A → M' A.
Arguments mlift {_ _ _ _}.
Hint Mode MLiftT ! ! : typeclass_instances.
Instance MLiftT_one `{MLift M M'} : MLiftT M M' := ltac:(assumption).
Instance MLiftT_trans `{MLift M' M'', MLiftT M M'} : MLiftT M M'' :=
  λ A x, mlift_in (mlift x).

(** idM can be lifted to any monad *)
Instance idM_lift_all `{MRet M} : MLift idM M := λ A x, mret x.


(** * Generic correctness typeclasses *)

Class Functor F `{FMap F} := {
    functor_id {A} : fmap id =@{F A → F A} id;
    functor_assoc {A B C} (f : A → B) (g : B → C) :
    fmap (g ∘ f) =@{F A → F C} fmap g ∘ fmap f
  }.

Class Monad M `{MRet M, MBind M} := {
    monad_left_id {A B} (a : A) (f : A → M B): mret a ≫= f = f a;
    monad_right_id : ∀ {A} (f : M A), f ≫= mret = f;
    monad_assoc : ∀ {A B C} (a : M A) (f : A → M B) (g : B → M C),
      a ≫= (λ x, f x ≫= g) = (a ≫= f) ≫= g;
  }.
Class MonadFMap M `{Monad M, FMap M} :=
  monad_fmap : ∀ {A B} (f : A → B), fmap f =@{M A → M B} mbind (λ x, mret (f x)).


Instance csimp_mon_left_id `{Monad M} {A B} (a : A) (f : A → M B) :
  mret a ≫= f ⇒ f a. Proof. apply monad_left_id. Qed.

Instance csimp_mon_right_id `{Monad M} {A} (f : M A) : f ≫= mret ⇒ f.
Proof. apply monad_right_id. Qed.

Instance csimp_monad_assoc `{Monad M} {A B C} (a : M A) (f : A → M B) (g : B → M C):
  a ≫= (λ x : A, f x ≫= g) ⇒ (a ≫= f) ≫= g.
Proof. apply monad_assoc. Qed.

Instance Functor_MonadFMap `{MonadFMap M} : Functor M.
Proof.
  split.
  - intros A.
    rewrite monad_fmap.
    extensionality x.
    by csimp.
  - intros A B C f g.
    rewrite ?monad_fmap.
    extensionality x.
    cbn.
    rewrite <- monad_assoc.
    setoid_rewrite monad_left_id.
    reflexivity.
Qed.

Lemma fmap_mret `{MonadFMap M} `(x : A) `(f : A → B) : f <$> mret x =@{M B} mret (f x).
Proof. rewrite monad_fmap. by csimp. Qed.

Instance csimp_fmap_mret `{MonadFMap M} {A B} (a : A) (f : A → B) :
  f <$> mret (M := M) a ⇒ mret (f a).
Proof. apply fmap_mret. Qed.
