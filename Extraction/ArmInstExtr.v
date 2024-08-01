Require Import SSCCommon.CExtraction.
Require Import GenModels.ArmSeqModel.

Unset Extraction SafeImplicits.

#[warnings="-extraction-remaining-implicit"]
Separate Extraction sequential_modelc.
