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

From ASCommon Require Import Options.
From ASCommon Require Import Common Exec FMon StateT.

Require Import Interface.
Require Import TermModels.


(** This module define helper function to manipulate ISA models. *)
Module ISAManip (IWA : InterfaceWithArch) (TM : TermModelsT IWA). (* to be imported *)
  Import IWA.Arch.
  Import IWA.Interface.
  Import TM.

  (** A global variable is a register that is always written before being read.
      This means it is never used for inter-instruction communication, and can
      therefore be safely be internalized in the instruction semantics.

      [remove_global_vars] takes the list of global variables to remove. It will
      crash if one of them is not a global variable, aka it is read before being
      written *)

  Section GlobalVars.
    Context (global_vars : gset reg).

    Equations remove_global_vars_handler :
      fHandler outcome (stateT registerMap iMon) :=
      remove_global_vars_handler (RegRead reg racc) :=
        if decide (reg ∈ global_vars) then
          entry ← mget (dmap_lookup reg);
          othrow
            ("Reading global variable " ++ pretty reg ++ " before writing it")%string
            entry
        else mcall (RegRead reg racc);
      remove_global_vars_handler (RegWrite reg racc rv) :=
        if decide (reg ∈ global_vars) then
          mSet (dmap_insert reg rv)
        else mcall (RegWrite reg racc rv);
      remove_global_vars_handler call := mcall call.

    Definition remove_global_vars `(isem : iMon A) : iMon A :=
      cinterp remove_global_vars_handler isem ∅ |$> snd.

    Definition remove_global_vars_trace_end `(itrce : fTraceEnd outcome A) : fTraceEnd outcome A :=
      match itrce with
      | FTEStop (RegRead reg _) => if decide (reg ∈ global_vars) then FTENothing else itrce
      | FTEStop (RegWrite reg _ _) => if decide (reg ∈ global_vars) then FTENothing else itrce
      | _ => itrce
      end.

    Definition remove_global_vars_traces `(itrc : iTrace A) : iTrace A :=
      (filter (λ ev, ¬ (is_reg_eventP (λ reg _ _, reg ∈ global_vars) ev)) itrc.1,
        remove_global_vars_trace_end itrc.2).

    Fixpoint global_vars_consistent_aux (itrc : list iEvent) (r : registerMap) :=
      match itrc with
      | RegRead reg _ &→ rv :: tl =>
          (reg ∈ global_vars → r !d! reg = Some rv) ∧ global_vars_consistent_aux tl r
      | RegWrite reg _ rv &→ _ :: tl =>
          global_vars_consistent_aux tl (if decide (reg ∈ global_vars) then dmap_insert reg rv r else r)
      | _ :: tl => global_vars_consistent_aux tl r
      | [] => True
      end.

    Instance global_vars_consistent_aux_dec itrc r :
      Decision (global_vars_consistent_aux itrc r).
    Proof. induction itrc as [ | [[]]] in r |- *; solve_decision. Defined.

    Definition global_vars_consistent `(itrc : iTrace A) :=
      global_vars_consistent_aux itrc.1 ∅.
    Instance global_vars_consistent_dec `(itrc : iTrace A) :
      Decision (global_vars_consistent itrc) := ltac:(unfold_decide).


    (* TODO automate using autorewrite in CDestruct rather than adding this *)
    #[local] Hint Extern 5 (CDestrSimpl _ ?P _) =>
      match P with
      | context [remove_global_vars_handler] =>
          constructor;
          progress (autorewrite with remove_global_vars_handler);
          reflexivity
      end : typeclass_instances.


    Lemma remove_global_vars_equiv `(isem : iMon A) (itrc : iTrace A) :
      global_vars_consistent itrc →
      cmatch isem itrc →
      cmatch (remove_global_vars isem) (remove_global_vars_traces itrc).
    Proof.
      destruct itrc as [trc trce].
      unfold remove_global_vars, cinterp, remove_global_vars_traces.
      cbn.
      generalize (∅ : registerMap) as rg.
      induction isem as [|[[]|[]]] in trc,trce |- * ; intros rg GVC.
      all: sinv 1.
      all: deintros.
      all: cdestruct |- *** #CDestrMatch.
      all: try econstructor.
      all: try naive_solver.
      csimp.
      unfold othrow.
      cdestruct |- *** #CDestrMatch #CDestrEqOpt.
      naive_solver.
    Qed.
  End GlobalVars.

End ISAManip.
