Require Import ASCommon.CExtraction.
Require Import ArchSemArm.ArmInst.

Unset Extraction SafeImplicits.

(* DO NOT run this file in your editor. This will extract in the correct folder
   when dune does the extraction *)
Set Extraction Output Directory ".".

#[warnings="-extraction-remaining-implicit"]
Separate Extraction sequential_modelc.
