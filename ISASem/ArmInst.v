Require Import Strings.String.
Require Import stdpp.unstable.bitvector.
Require Import Interface.
Require Export SailArmInst_types.


Module Arm <: Arch.
  Definition reg := string.
  Definition reg_type := register_value.
  Definition va_size := 64%N.
  Definition pa := FullAddress.
  Definition arch_ak := arm_acc_type.
  Definition translation := TranslationInfo.
  Definition abort := PhysMemRetStatus.
  Definition barrier := Barrier.
  Definition cache_op := CacheRecord.
  Definition tlb_op := TLBI.
  Definition fault := Exn.
End Arm.

Module Inst := Interface Arm.

Export Inst.
