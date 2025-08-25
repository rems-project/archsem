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

(** Coq configuration for ArchSem (not meant to leak to clients).

Any downstream project should have its own options file as this might change at
any time without notice.

All ArchSem files should Import (but not Export) this.
This file should be imported before any other ArchSem file *)
(* Everything here should be [#[export] Set], which means when this
file is *imported*, the option will only apply on the import site
but not transitively. *)

(** Force [Proof.] commands in section to just be [Proof using.]. This means the
    code must specify any section variables, and that most lemmas that don't
    need any extra section variable can just start with [Proof.] and not
    [Proof using.] *)
#[export] Set Default Proof Using "".

(** Enforces that every tactic is executed with a single focused goal, meaning
    that bullets and curly braces must be used to structure the proof. *)
#[export] Set Default Goal Selector "!".

(** Improve the behavior of unification for rewriting tactics, at the cost of
    making rewriting a bit slower *)
#[export] Set Keyed Unification.

(** Disable Fancy program pattern matching. The equality can be recovered (if
needed) with [inspect] *)
#[export] Unset Program Cases.

(** We want [idtac] by default *)
#[export] Obligation Tactic := idtac.

(** Use the if _ is _ notation in this project, but do not force users to use it *)
Export IfNotations.

(** Make typeclass resolution treat all constant as opaque by default *)
#[export] Hint Constants Opaque : typeclass_instances.

Require Import stdpp.base.

(** Functional pipe notation. *)
Module FunctionPipeNotations.

  Notation "v |> f" := (f v) (at level 68, only parsing, left associativity).

  (** And pipes for  FMap notations *)
  Notation "v |$> f" := (fmap f v) (at level 68, only parsing, left associativity).
  Notation "v |$>@{ M } f" := (@fmap M _ _ _ f v)
                                (at level 68, only parsing, left associativity).
End FunctionPipeNotations.
Export FunctionPipeNotations.


(* TODO automatically check that all file in the project import this file.
   This might be done with a text checker that there exists a
   [Require Import Options.] or [Require Import ASCommon.Options] *)
