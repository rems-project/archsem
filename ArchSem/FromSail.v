(** This file is dedicated to building SSC Interface instance from a sail
    generated coq model. The only part that is not automatically generated by
    now is pa manipulation functions *)


Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import SailStdpp.ConcurrencyInterface.
Require Import SailStdpp.Values.
Require Import SailStdpp.Instances.

Module Type SailArch := Arch.
Module Type SailInterfaceT := InterfaceT.

Require Import ASCommon.Options.
Require Import ASCommon.Common.
Require Import ASCommon.Effects.

Require Import ASCommon.FMon.
Require Import Interface.

(** * Transparency management for [coq-sail] *)
#[export] Typeclasses Transparent choose_type.
#[export] Typeclasses Transparent mword.
#[export] Typeclasses Transparent MachineWord.MachineWord.word.
#[export] Typeclasses Transparent MachineWord.MachineWord.idx.
#[export] Typeclasses Transparent MachineWord.MachineWord.Z_idx.

(* TODO go in coq-sail and make those not exist *)
Arguments MachineWord.MachineWord.word / _.
Arguments MachineWord.MachineWord.idx /.
Arguments MachineWord.MachineWord.Z_idx / _.

(* TODO remove that in coq-sail *)
Remove Hints Decidable_eq_mword : typeclass_instances.

(** * Missing Interface parts

This section defines a module type that describes everything ArchSem need from
an architecture instantiation that is missing from the Sail generated code *)
Module Type PAManip (SA : SailArch).
  Import SA.
  (** Add an offset to a physical address. Can wrap if out of bounds *)
  Parameter pa_addZ : pa → Z → pa.

  (** This need to behave sensibly.
      For fancy words: pa_addZ need to be an action of the group Z on pa *)
  Parameter pa_addZ_assoc :
    ∀ pa z z', pa_addZ (pa_addZ pa z) z' = pa_addZ pa (z + z')%Z.
  Parameter pa_addZ_zero : ∀ pa, pa_addZ pa 0 = pa.
  #[export] Hint Rewrite pa_addZ_assoc : arch.
  #[export] Hint Rewrite pa_addZ_zero : arch.

  Parameter pa_diffN : pa → pa → option N.
  Parameter pa_diffN_addZ:
    ∀ pa pa' n, pa_diffN pa' pa = Some n → pa_addZ pa (Z.of_N n) = pa'.
  Parameter pa_diffN_existZ:
    ∀ pa pa' z, pa_addZ pa z = pa' → is_Some (pa_diffN pa' pa).
  Parameter pa_diffN_minimalZ:
    ∀ pa pa' n, pa_diffN pa' pa = Some n →
                ∀ z', pa_addZ pa z' = pa' → (z' < 0 ∨ (Z.of_N n) ≤ z')%Z.

  (* Extra stuff that shouldn't be there *)

  Parameter pc_reg : greg.

End PAManip.

(** * Convert from Sail generated instantiations to ArchSem ones *)

Module ArchFromSail (SA : SailArch) (PAM : PAManip SA) <: Arch.
  Include PAM.
  Import (hints) SA.
  Definition reg := SA.greg.
  #[export] Instance reg_eq : EqDecision reg := SA.greg_eq.
  #[export] Instance reg_countable : Countable reg := SA.greg_cnt.

  Definition reg_type (r : reg) := match r with @SA.GReg A _ => A end.
  #[export] Instance reg_type_eq (r : reg) : EqDecision (reg_type r).
  Proof. destruct r. by apply SA.regval_eq. Defined.
  #[export] Instance reg_type_countable (r : reg) : Countable (reg_type r).
  Proof. destruct r. by apply SA.regval_cnt. Defined.
  #[export] Instance reg_type_inhabited (r : reg) : Inhabited (reg_type r).
  Proof. destruct r. by apply SA.regval_inhabited. Defined.
  #[export] Instance ctrans_reg_type : CTrans reg_type.
  Proof.
    intros [Tx x] [Ty y] e a. cbn in *.
    by eapply SA.regval_transport.
  Defined.
  #[export] Instance ctrans_reg_type_simpl : CTransSimpl reg_type.
  Proof. intros [Tx x] e a. apply SA.regval_transport_sound. Qed.
  #[export] Instance reg_type_eq_dep_dec : EqDepDecision reg_type.
  Proof.
    intros [Tx x] [Ty y] e a b.
    refine (dec_if (decide (ctrans e a = b)));
      abstract (dependent destruction e; simp ctrans in *; by rewrite JMeq_simpl).
  Defined.

  (* TODO get sail to generate reg_acc *)
  Definition reg_acc := option SA.sys_reg_id.
  #[local] Typeclasses Transparent reg_acc.
  Existing Instance SA.sys_reg_id_eq.
  Definition reg_acc_eq : EqDecision reg_acc := _.

  Definition va_size := SA.va_size.
  Definition pa := SA.pa.
  Definition pa_eq := SA.pa_eq.
  Definition pa_countable := SA.pa_countable.

  Definition mem_acc := Access_kind SA.arch_ak.
  #[local] Typeclasses Transparent mem_acc.
  Definition mem_acc_eq : EqDecision mem_acc := _.
  Definition is_explicit (acc : mem_acc) :=
    if acc is AK_explicit _ then true else false.
  Definition is_ifetch (acc : mem_acc) :=
    if acc is AK_ifetch _ then true else false.
  Definition is_ttw (acc : mem_acc) :=
    if acc is AK_ttw _ then true else false.
  Definition is_relaxed (acc : mem_acc) :=
    if acc is AK_explicit eak then
      eak.(Explicit_access_kind_strength) =? AS_normal else false.
  Definition is_rel_acq (acc : mem_acc) :=
    if acc is AK_explicit eak then
      eak.(Explicit_access_kind_strength) =? AS_rel_or_acq else false.
  Definition is_acq_rcpc (acc : mem_acc) :=
    if acc is AK_explicit eak then
      eak.(Explicit_access_kind_strength) =? AS_acq_rcpc else false.
  Definition is_standalone (acc : mem_acc) :=
    if acc is AK_explicit eak then
      eak.(Explicit_access_kind_variety) =? AV_plain else false.
  Definition is_exclusive (acc : mem_acc) :=
    if acc is AK_explicit eak then
      eak.(Explicit_access_kind_variety) =? AV_exclusive else false.
  Definition is_atomic_rmw (acc : mem_acc) :=
    if acc is AK_explicit eak then
      eak.(Explicit_access_kind_variety) =? AV_atomic_rmw else false.

  Definition translation := SA.translation.
  Definition translation_eq := SA.translation_eq.
  Definition abort := SA.abort.

  Definition barrier := SA.barrier.
  Definition barrier_eq := SA.barrier_eq.
  Definition cache_op := SA.cache_op.
  Definition cache_op_eq := SA.cache_op_eq.
  Definition tlb_op := SA.tlb_op.
  Definition tlb_op_eq := SA.tlb_op_eq.
  Definition fault := SA.fault .
  Definition fault_eq := SA.fault_eq.
  Definition trans_start := SA.trans_start.
  Definition trans_start_eq := SA.trans_start_eq.
  Definition trans_end := SA.trans_end.
  Definition trans_end_eq := SA.trans_end_eq.
End ArchFromSail.

Module Type ArchFromSailT (SA : SailArch) (PAM : PAManip SA).
  Include ArchFromSail SA PAM.
End ArchFromSailT.


Module IMonFromSail (SA : SailArch) (SI : SailInterfaceT SA)
  (PAM : PAManip SA) (Arch : ArchFromSailT SA PAM) (I : InterfaceT Arch).
  Import Arch.
  Import I.
  Import (coercions) SA.

  Definition ReadReq_from_sail {n} (rr : SI.ReadReq.t n) : ReadReq.t n :=
    {|ReadReq.pa := rr.(SI.ReadReq.pa);
      ReadReq.access_kind := rr.(SI.ReadReq.access_kind);
      ReadReq.va := rr.(SI.ReadReq.va);
      ReadReq.translation := rr.(SI.ReadReq.translation);
      ReadReq.tag := rr.(SI.ReadReq.tag)
    |}.

  Definition WriteReq_from_sail {n} (rr : SI.WriteReq.t n) : WriteReq.t n :=
    {|WriteReq.pa := rr.(SI.WriteReq.pa);
      WriteReq.access_kind := rr.(SI.WriteReq.access_kind);
      WriteReq.va := rr.(SI.WriteReq.va);
      WriteReq.value := rr.(SI.WriteReq.value);
      WriteReq.translation := rr.(SI.WriteReq.translation);
      WriteReq.tag := rr.(SI.WriteReq.tag)
    |}.

  Definition Sail_outcome_interp {A eo} (out : SI.outcome eo A) : I.iMon A :=
    match out with
    | SI.RegRead reg acc => mcall (RegRead reg acc)
    | SI.RegWrite reg acc regval => mcall (RegWrite reg acc regval)
    | SI.MemRead n rr => mcall (MemRead n (ReadReq_from_sail rr))
    | SI.MemWrite n wr =>
        mcall (MemWrite n (WriteReq_from_sail wr)) |$> mapl Some
    | SI.InstrAnnounce _ => mret ()
    | SI.BranchAnnounce _ _ => mret ()
    | SI.Barrier b => mcall (Barrier b)
    | SI.CacheOp cop => mcall (CacheOp cop)
    | SI.TlbOp top => mcall (TlbOp top)
    | SI.TakeException fault => mcall (TakeException fault)
    | SI.ReturnException _ => mcall ReturnException
    | SI.TranslationStart ts => mcall (TranslationStart ts)
    | SI.TranslationEnd te => mcall (TranslationEnd te)
    | SI.GenericFail msg => mcall_noret (GenericFail msg)
    | SI.CycleCount => mret ()
    | SI.GetCycleCount => mcall_noret (GenericFail "GetCycleCount not supported")
    | SI.Choose ChooseBool => mchoosef
    | SI.Choose (ChooseBitvector n) => mchoosef (* might blow up *)
    | SI.Choose _ => mcall_noret (GenericFail "Choosing non boolean in Sail")
    | SI.Discard => mdiscard
    | SI.ExtraOutcome e => mcall_noret (GenericFail "ExtraOutcome not supported")
    end.

  Fixpoint iMon_from_Sail {A eo} (smon: SI.iMon eo A): I.iMon A :=
    match smon with
    | SI.Ret a => mret a
    | SI.Next out k =>
        r ← Sail_outcome_interp out;
        iMon_from_Sail (k r)
    end.
End IMonFromSail.
