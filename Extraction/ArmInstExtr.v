Require Import ASCommon.CExtraction.
From ArchSemArm Require Import ArmInst UMPromising VMPromising.

Unset Extraction SafeImplicits.

Extract Inductive ArchSem.Interface.reg_gen_val =>
  "Reggenval.gen"
  ["Reggenval.Number" "Reggenval.String" "Reggenval.Array" "Reggenval.Struct"].

(* DO NOT run this file in your editor. This will extract in the correct folder
   when dune does the extraction *)
Set Extraction Output Directory ".".

(* Definition umProm_cert_c := UMPromising_cert_c. *)

#[warnings="-extraction-remaining-implicit,-extraction-reserved-identifier"]
Separate Extraction sequential_modelc sail_tiny_arm_sem Arm UMPromising_cert_c.
