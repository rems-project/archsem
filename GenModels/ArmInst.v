(** This module is the Arm-A v8/9 instantiation of all the GenModels modules
    based on the interface instantiation in ISASem.ArmInst *)

Require Export ISASem.ArmInst.
Require Import GenModels.TermModels.
Module ArmTM := TermModels Arm.
Require Import GenModels.CandidateExecutions.
Module ArmCand := CandidateExecutions Arm ArmTM.

Export ArmTM.
Export ArmCand.
