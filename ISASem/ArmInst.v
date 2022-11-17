Require Import Strings.String.
Require Import stdpp.unstable.bitvector.
Require Import Interface.
Require Import Sail.Base.
Require Export SailArmInstTypes.
Require Import Coq.Reals.Reals.
From RecordUpdate Require Import RecordSet.

Inductive regval  :=
  | Regval_unknown : regval
  | Regval_vector : list regval -> regval
  | Regval_list : list regval -> regval
  | Regval_option : option regval -> regval
  | Regval_bool : bool -> regval
  | Regval_int : Z -> regval
  | Regval_real : R -> regval
  | Regval_string : string -> regval
  | Regval_bitvector z : mword z -> regval
  | Regval_struct : list (string * regval) -> regval.

#[global] Instance FullAddress_eta : Settable _ :=
  settable! Build_FullAddress <FullAddress_paspace; FullAddress_address>.

Module Arm <: Arch.
  Definition reg := string.
  Definition reg_type := regval.
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
