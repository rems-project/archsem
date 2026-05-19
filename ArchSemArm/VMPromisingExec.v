(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
(*      Shreeka Lohani, University of Cambridge                               *)
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
From ASCommon Require Import Common GRel Exec FMon StateT HVec.

From ArchSem Require Import GenPromising.
From ArchSemArm Require Import ArmInst VMPromising.

#[local] Open Scope list.
#[local] Open Scope nat.
#[local] Open Scope stdpp.

Definition VMPromising_nocert (bbm_param : BBM.param) :=
  Promising_to_Modelnc (*certified=*)false (VMPromising bbm_param).

Definition VMPromising_cert (bbm_param : BBM.param) :=
  Promising_to_Modelnc (*certified=*)true (VMPromising bbm_param).

Definition VMPromising_exe (bbm_param : BBM.param) :=
  Promising_to_Modelc (VMPromising bbm_param).

Definition VMPromising_pf (bbm_param : BBM.param) :=
  Promising_to_Modelc_pf (VMPromising bbm_param).

Definition VMPromising_final_state (bbm_param : BBM.param) {n}
    (isem : iMon ()) (term : terminationCondition n) initMs fs : Prop :=
  ∃ fuel pt,
    archModel.Res.FinalState fs pt ∈
      VMPromising_exe bbm_param isem fuel n term initMs.

Definition VMPromising_pf_final_state (bbm_param : BBM.param) {n}
    (isem : iMon ()) (term : terminationCondition n) initMs fs : Prop :=
  ∃ fuel pt,
    archModel.Res.FinalState fs pt ∈
      VMPromising_pf bbm_param isem fuel n term initMs.
