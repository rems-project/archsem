Require Import Sail.Base.
Require Import Sail.Real.
Require Import stdpp.unstable.bitvector.
Import ListNotations.
Open Scope string.
Open Scope bool.
Open Scope Z.

Inductive Access_strength := AS_normal | AS_rel_or_acq | AS_acq_rcpc.
Scheme Equality for Access_strength.
#[export] Instance Decidable_eq_Access_strength :
forall (x y : Access_strength), Decidable (x = y) :=
Decidable_eq_from_dec Access_strength_eq_dec.

Inductive Access_variety := AV_plain | AV_exclusive | AV_atomic_rmw.
Scheme Equality for Access_variety.
#[export] Instance Decidable_eq_Access_variety :
forall (x y : Access_variety), Decidable (x = y) :=
Decidable_eq_from_dec Access_variety_eq_dec.

Definition bits (n : Z) :=
  match n with
  | Zneg _ => bv 0
  | Z0 => bv 0
  | Zpos p => bv (Npos p)
  end.

Inductive result {a : Type} {b : Type} := | Ok : a -> result | Err : b -> result.
Arguments result : clear implicits.

Record Explicit_access_kind  :=
  { Explicit_access_kind_variety : Access_variety; Explicit_access_kind_strength : Access_strength; }.
Arguments Explicit_access_kind : clear implicits.
Notation "{[ r 'with' 'Explicit_access_kind_variety' := e ]}" :=
  match r with Build_Explicit_access_kind _ f1 => Build_Explicit_access_kind e f1 end.
Notation "{[ r 'with' 'Explicit_access_kind_strength' := e ]}" :=
  match r with Build_Explicit_access_kind f0 _ => Build_Explicit_access_kind f0 e end.

Inductive Access_kind {arch_ak : Type} :=
  | AK_explicit : Explicit_access_kind -> Access_kind
  | AK_ifetch : unit -> Access_kind
  | AK_ttw : unit -> Access_kind
  | AK_arch : arch_ak -> Access_kind.
Arguments Access_kind : clear implicits.

Record Mem_read_request {n : Z} {vasize : Z} {pa : Type} {ts : Type} {arch_ak : Type}`{ArithFact (n >?
  0)} :=
  { Mem_read_request_access_kind : Access_kind arch_ak;
    Mem_read_request_va : option (bits vasize);
    Mem_read_request_pa : pa;
    Mem_read_request_translation : ts;
    Mem_read_request_size : Z;
    Mem_read_request_tag : bool; }.
Arguments Mem_read_request _ _ _ _ _ {_}.
Notation "{[ r 'with' 'Mem_read_request_access_kind' := e ]}" :=
  match r with Build_Mem_read_request _ _ _ _ _ _ _ f1 f2 f3 f4 f5 =>
    Build_Mem_read_request _ _ _ _ _ e f1 f2 f3 f4 f5 end.
Notation "{[ r 'with' 'Mem_read_request_va' := e ]}" :=
  match r with Build_Mem_read_request _ _ _ _ _ _ f0 _ f2 f3 f4 f5 =>
    Build_Mem_read_request _ _ _ _ _ f0 e f2 f3 f4 f5 end.
Notation "{[ r 'with' 'Mem_read_request_pa' := e ]}" :=
  match r with Build_Mem_read_request _ _ _ _ _ _ f0 f1 _ f3 f4 f5 =>
    Build_Mem_read_request _ _ _ _ _ f0 f1 e f3 f4 f5 end.
Notation "{[ r 'with' 'Mem_read_request_translation' := e ]}" :=
  match r with Build_Mem_read_request _ _ _ _ _ _ f0 f1 f2 _ f4 f5 =>
    Build_Mem_read_request _ _ _ _ _ f0 f1 f2 e f4 f5 end.
Notation "{[ r 'with' 'Mem_read_request_size' := e ]}" :=
  match r with Build_Mem_read_request _ _ _ _ _ _ f0 f1 f2 f3 _ f5 =>
    Build_Mem_read_request _ _ _ _ _ f0 f1 f2 f3 e f5 end.
Notation "{[ r 'with' 'Mem_read_request_tag' := e ]}" :=
  match r with Build_Mem_read_request _ _ _ _ _ _ f0 f1 f2 f3 f4 _ =>
    Build_Mem_read_request _ _ _ _ _ f0 f1 f2 f3 f4 e end.

Record Mem_write_request {n : Z} {vasize : Z} {pa : Type} {ts : Type} {arch_ak : Type}`{ArithFact (n >?
  0)} :=
  { Mem_write_request_access_kind : Access_kind arch_ak;
    Mem_write_request_va : option (bits vasize);
    Mem_write_request_pa : pa;
    Mem_write_request_translation : ts;
    Mem_write_request_size : Z;
    Mem_write_request_value : option (bits (8 * n));
    Mem_write_request_tag : option bool; }.
Arguments Mem_write_request _ _ _ _ _ {_}.
Notation "{[ r 'with' 'Mem_write_request_access_kind' := e ]}" :=
  match r with Build_Mem_write_request _ _ _ _ _ _ _ f1 f2 f3 f4 f5 f6 =>
    Build_Mem_write_request _ _ _ _ _ e f1 f2 f3 f4 f5 f6 end.
Notation "{[ r 'with' 'Mem_write_request_va' := e ]}" :=
  match r with Build_Mem_write_request _ _ _ _ _ _ f0 _ f2 f3 f4 f5 f6 =>
    Build_Mem_write_request _ _ _ _ _ f0 e f2 f3 f4 f5 f6 end.
Notation "{[ r 'with' 'Mem_write_request_pa' := e ]}" :=
  match r with Build_Mem_write_request _ _ _ _ _ _ f0 f1 _ f3 f4 f5 f6 =>
    Build_Mem_write_request _ _ _ _ _ f0 f1 e f3 f4 f5 f6 end.
Notation "{[ r 'with' 'Mem_write_request_translation' := e ]}" :=
  match r with Build_Mem_write_request _ _ _ _ _ _ f0 f1 f2 _ f4 f5 f6 =>
    Build_Mem_write_request _ _ _ _ _ f0 f1 f2 e f4 f5 f6 end.
Notation "{[ r 'with' 'Mem_write_request_size' := e ]}" :=
  match r with Build_Mem_write_request _ _ _ _ _ _ f0 f1 f2 f3 _ f5 f6 =>
    Build_Mem_write_request _ _ _ _ _ f0 f1 f2 f3 e f5 f6 end.
Notation "{[ r 'with' 'Mem_write_request_value' := e ]}" :=
  match r with Build_Mem_write_request _ _ _ _ _ _ f0 f1 f2 f3 f4 _ f6 =>
    Build_Mem_write_request _ _ _ _ _ f0 f1 f2 f3 f4 e f6 end.
Notation "{[ r 'with' 'Mem_write_request_tag' := e ]}" :=
  match r with Build_Mem_write_request _ _ _ _ _ _ f0 f1 f2 f3 f4 f5 _ =>
    Build_Mem_write_request _ _ _ _ _ f0 f1 f2 f3 f4 f5 e end.

Record Mem_write_announce_address {n : Z} {vasize : Z} {pa : Type} :=
  { Mem_write_announce_address_pa : pa; Mem_write_announce_address_size : Z; }.
Arguments Mem_write_announce_address : clear implicits.
Notation "{[ r 'with' 'Mem_write_announce_address_pa' := e ]}" :=
  match r with Build_Mem_write_announce_address _ _ _ _ f1 =>
    Build_Mem_write_announce_address _ _ _ e f1 end.
Notation "{[ r 'with' 'Mem_write_announce_address_size' := e ]}" :=
  match r with Build_Mem_write_announce_address _ _ _ f0 _ =>
    Build_Mem_write_announce_address _ _ _ f0 e end.

Inductive Exception :=
  Exception_Uncategorized
  | Exception_WFxTrap
  | Exception_CP15RTTrap
  | Exception_CP15RRTTrap
  | Exception_CP14RTTrap
  | Exception_CP14DTTrap
  | Exception_CP14RRTTrap
  | Exception_AdvSIMDFPAccessTrap
  | Exception_FPIDTrap
  | Exception_LDST64BTrap
  | Exception_PACTrap
  | Exception_IllegalState
  | Exception_SupervisorCall
  | Exception_HypervisorCall
  | Exception_MonitorCall
  | Exception_SystemRegisterTrap
  | Exception_ERetTrap
  | Exception_InstructionAbort
  | Exception_PCAlignment
  | Exception_DataAbort
  | Exception_NV2DataAbort
  | Exception_PACFail
  | Exception_SPAlignment
  | Exception_FPTrappedException
  | Exception_SError
  | Exception_Breakpoint
  | Exception_SoftwareStep
  | Exception_Watchpoint
  | Exception_NV2Watchpoint
  | Exception_SoftwareBreakpoint
  | Exception_VectorCatch
  | Exception_IRQ
  | Exception_SVEAccessTrap
  | Exception_SMEAccessTrap
  | Exception_TSTARTAccessTrap
  | Exception_GPC
  | Exception_BranchTarget
  | Exception_MemCpyMemSet
  | Exception_FIQ.
Scheme Equality for Exception.
#[export] Instance Decidable_eq_Exception :
forall (x y : Exception), Decidable (x = y) :=
Decidable_eq_from_dec Exception_eq_dec.

Inductive PASpace := PAS_NonSecure | PAS_Secure | PAS_Root | PAS_Realm.
Scheme Equality for PASpace.
#[export] Instance Decidable_eq_PASpace :
forall (x y : PASpace), Decidable (x = y) :=
Decidable_eq_from_dec PASpace_eq_dec.

Record FullAddress  := { FullAddress_paspace : PASpace; FullAddress_address : bits 52; }.
Arguments FullAddress : clear implicits.
Notation "{[ r 'with' 'FullAddress_paspace' := e ]}" :=
  match r with Build_FullAddress _ f1 => Build_FullAddress e f1 end.
Notation "{[ r 'with' 'FullAddress_address' := e ]}" :=
  match r with Build_FullAddress f0 _ => Build_FullAddress f0 e end.

Record ExceptionRecord  :=
  { ExceptionRecord_exceptype : Exception;
    ExceptionRecord_syndrome : bits 25;
    ExceptionRecord_syndrome2 : bits 5;
    ExceptionRecord_paddress : FullAddress;
    ExceptionRecord_vaddress : bits 64;
    ExceptionRecord_ipavalid : bool;
    ExceptionRecord_NS : bits 1;
    ExceptionRecord_ipaddress : bits 52;
    ExceptionRecord_trappedsyscallinst : bool; }.
Arguments ExceptionRecord : clear implicits.
Notation "{[ r 'with' 'ExceptionRecord_exceptype' := e ]}" :=
  match r with Build_ExceptionRecord _ f1 f2 f3 f4 f5 f6 f7 f8 =>
    Build_ExceptionRecord e f1 f2 f3 f4 f5 f6 f7 f8 end.
Notation "{[ r 'with' 'ExceptionRecord_syndrome' := e ]}" :=
  match r with Build_ExceptionRecord f0 _ f2 f3 f4 f5 f6 f7 f8 =>
    Build_ExceptionRecord f0 e f2 f3 f4 f5 f6 f7 f8 end.
Notation "{[ r 'with' 'ExceptionRecord_syndrome2' := e ]}" :=
  match r with Build_ExceptionRecord f0 f1 _ f3 f4 f5 f6 f7 f8 =>
    Build_ExceptionRecord f0 f1 e f3 f4 f5 f6 f7 f8 end.
Notation "{[ r 'with' 'ExceptionRecord_paddress' := e ]}" :=
  match r with Build_ExceptionRecord f0 f1 f2 _ f4 f5 f6 f7 f8 =>
    Build_ExceptionRecord f0 f1 f2 e f4 f5 f6 f7 f8 end.
Notation "{[ r 'with' 'ExceptionRecord_vaddress' := e ]}" :=
  match r with Build_ExceptionRecord f0 f1 f2 f3 _ f5 f6 f7 f8 =>
    Build_ExceptionRecord f0 f1 f2 f3 e f5 f6 f7 f8 end.
Notation "{[ r 'with' 'ExceptionRecord_ipavalid' := e ]}" :=
  match r with Build_ExceptionRecord f0 f1 f2 f3 f4 _ f6 f7 f8 =>
    Build_ExceptionRecord f0 f1 f2 f3 f4 e f6 f7 f8 end.
Notation "{[ r 'with' 'ExceptionRecord_NS' := e ]}" :=
  match r with Build_ExceptionRecord f0 f1 f2 f3 f4 f5 _ f7 f8 =>
    Build_ExceptionRecord f0 f1 f2 f3 f4 f5 e f7 f8 end.
Notation "{[ r 'with' 'ExceptionRecord_ipaddress' := e ]}" :=
  match r with Build_ExceptionRecord f0 f1 f2 f3 f4 f5 f6 _ f8 =>
    Build_ExceptionRecord f0 f1 f2 f3 f4 f5 f6 e f8 end.
Notation "{[ r 'with' 'ExceptionRecord_trappedsyscallinst' := e ]}" :=
  match r with Build_ExceptionRecord f0 f1 f2 f3 f4 f5 f6 f7 _ =>
    Build_ExceptionRecord f0 f1 f2 f3 f4 f5 f6 f7 e end.

Inductive SecurityState := SS_NonSecure | SS_Root | SS_Realm | SS_Secure.
Scheme Equality for SecurityState.
#[export] Instance Decidable_eq_SecurityState :
forall (x y : SecurityState), Decidable (x = y) :=
Decidable_eq_from_dec SecurityState_eq_dec.

Inductive AccType :=
  AccType_NORMAL
  | AccType_STREAM
  | AccType_VEC
  | AccType_VECSTREAM
  | AccType_SVE
  | AccType_SVESTREAM
  | AccType_SME
  | AccType_SMESTREAM
  | AccType_UNPRIVSTREAM
  | AccType_A32LSMD
  | AccType_ATOMIC
  | AccType_ATOMICRW
  | AccType_ORDERED
  | AccType_ORDEREDRW
  | AccType_ORDEREDATOMIC
  | AccType_ORDEREDATOMICRW
  | AccType_ATOMICLS64
  | AccType_LIMITEDORDERED
  | AccType_UNPRIV
  | AccType_IFETCH
  | AccType_TTW
  | AccType_NONFAULT
  | AccType_CNOTFIRST
  | AccType_NV2REGISTER
  | AccType_DC
  | AccType_IC
  | AccType_DCZVA
  | AccType_ATPAN
  | AccType_AT.
Scheme Equality for AccType.
#[export] Instance Decidable_eq_AccType :
forall (x y : AccType), Decidable (x = y) :=
Decidable_eq_from_dec AccType_eq_dec.

Inductive Fault :=
  Fault_None
  | Fault_AccessFlag
  | Fault_Alignment
  | Fault_Background
  | Fault_Domain
  | Fault_Permission
  | Fault_Translation
  | Fault_AddressSize
  | Fault_SyncExternal
  | Fault_SyncExternalOnWalk
  | Fault_SyncParity
  | Fault_SyncParityOnWalk
  | Fault_GPCFOnWalk
  | Fault_GPCFOnOutput
  | Fault_AsyncParity
  | Fault_AsyncExternal
  | Fault_Debug
  | Fault_TLBConflict
  | Fault_BranchTarget
  | Fault_HWUpdateAccessFlag
  | Fault_Lockdown
  | Fault_Exclusive
  | Fault_ICacheMaint.
Scheme Equality for Fault.
#[export] Instance Decidable_eq_Fault :
forall (x y : Fault), Decidable (x = y) :=
Decidable_eq_from_dec Fault_eq_dec.

Inductive GPCF := GPCF_None | GPCF_AddressSize | GPCF_Walk | GPCF_EABT | GPCF_Fail.
Scheme Equality for GPCF.
#[export] Instance Decidable_eq_GPCF :
forall (x y : GPCF), Decidable (x = y) :=
Decidable_eq_from_dec GPCF_eq_dec.

Record GPCFRecord  := { GPCFRecord_gpf : GPCF; GPCFRecord_level : Z; }.
Arguments GPCFRecord : clear implicits.
Notation "{[ r 'with' 'GPCFRecord_gpf' := e ]}" :=
  match r with Build_GPCFRecord _ f1 => Build_GPCFRecord e f1 end.
Notation "{[ r 'with' 'GPCFRecord_level' := e ]}" :=
  match r with Build_GPCFRecord f0 _ => Build_GPCFRecord f0 e end.

Record FaultRecord  :=
  { FaultRecord_statuscode : Fault;
    FaultRecord_acctype : AccType;
    FaultRecord_ipaddress : FullAddress;
    FaultRecord_gpcf : GPCFRecord;
    FaultRecord_paddress : FullAddress;
    FaultRecord_gpcfs2walk : bool;
    FaultRecord_s2fs1walk : bool;
    FaultRecord_write : bool;
    FaultRecord_level : Z;
    FaultRecord_extflag : bits 1;
    FaultRecord_secondstage : bool;
    FaultRecord_domain : bits 4;
    FaultRecord_errortype : bits 2;
    FaultRecord_debugmoe : bits 4; }.
Arguments FaultRecord : clear implicits.
Notation "{[ r 'with' 'FaultRecord_statuscode' := e ]}" :=
  match r with Build_FaultRecord _ f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 =>
    Build_FaultRecord e f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 end.
Notation "{[ r 'with' 'FaultRecord_acctype' := e ]}" :=
  match r with Build_FaultRecord f0 _ f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 =>
    Build_FaultRecord f0 e f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 end.
Notation "{[ r 'with' 'FaultRecord_ipaddress' := e ]}" :=
  match r with Build_FaultRecord f0 f1 _ f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 =>
    Build_FaultRecord f0 f1 e f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 end.
Notation "{[ r 'with' 'FaultRecord_gpcf' := e ]}" :=
  match r with Build_FaultRecord f0 f1 f2 _ f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 =>
    Build_FaultRecord f0 f1 f2 e f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 end.
Notation "{[ r 'with' 'FaultRecord_paddress' := e ]}" :=
  match r with Build_FaultRecord f0 f1 f2 f3 _ f5 f6 f7 f8 f9 f10 f11 f12 f13 =>
    Build_FaultRecord f0 f1 f2 f3 e f5 f6 f7 f8 f9 f10 f11 f12 f13 end.
Notation "{[ r 'with' 'FaultRecord_gpcfs2walk' := e ]}" :=
  match r with Build_FaultRecord f0 f1 f2 f3 f4 _ f6 f7 f8 f9 f10 f11 f12 f13 =>
    Build_FaultRecord f0 f1 f2 f3 f4 e f6 f7 f8 f9 f10 f11 f12 f13 end.
Notation "{[ r 'with' 'FaultRecord_s2fs1walk' := e ]}" :=
  match r with Build_FaultRecord f0 f1 f2 f3 f4 f5 _ f7 f8 f9 f10 f11 f12 f13 =>
    Build_FaultRecord f0 f1 f2 f3 f4 f5 e f7 f8 f9 f10 f11 f12 f13 end.
Notation "{[ r 'with' 'FaultRecord_write' := e ]}" :=
  match r with Build_FaultRecord f0 f1 f2 f3 f4 f5 f6 _ f8 f9 f10 f11 f12 f13 =>
    Build_FaultRecord f0 f1 f2 f3 f4 f5 f6 e f8 f9 f10 f11 f12 f13 end.
Notation "{[ r 'with' 'FaultRecord_level' := e ]}" :=
  match r with Build_FaultRecord f0 f1 f2 f3 f4 f5 f6 f7 _ f9 f10 f11 f12 f13 =>
    Build_FaultRecord f0 f1 f2 f3 f4 f5 f6 f7 e f9 f10 f11 f12 f13 end.
Notation "{[ r 'with' 'FaultRecord_extflag' := e ]}" :=
  match r with Build_FaultRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 _ f10 f11 f12 f13 =>
    Build_FaultRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 e f10 f11 f12 f13 end.
Notation "{[ r 'with' 'FaultRecord_secondstage' := e ]}" :=
  match r with Build_FaultRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 _ f11 f12 f13 =>
    Build_FaultRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e f11 f12 f13 end.
Notation "{[ r 'with' 'FaultRecord_domain' := e ]}" :=
  match r with Build_FaultRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 _ f12 f13 =>
    Build_FaultRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 e f12 f13 end.
Notation "{[ r 'with' 'FaultRecord_errortype' := e ]}" :=
  match r with Build_FaultRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _ f13 =>
    Build_FaultRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 e f13 end.
Notation "{[ r 'with' 'FaultRecord_debugmoe' := e ]}" :=
  match r with Build_FaultRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 _ =>
    Build_FaultRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 e end.

Inductive DeviceType := DeviceType_GRE | DeviceType_nGRE | DeviceType_nGnRE | DeviceType_nGnRnE.
Scheme Equality for DeviceType.
#[export] Instance Decidable_eq_DeviceType :
forall (x y : DeviceType), Decidable (x = y) :=
Decidable_eq_from_dec DeviceType_eq_dec.

Record MemAttrHints  :=
  { MemAttrHints_attrs : bits 2; MemAttrHints_hints : bits 2; MemAttrHints_transient : bool; }.
Arguments MemAttrHints : clear implicits.
Notation "{[ r 'with' 'MemAttrHints_attrs' := e ]}" :=
  match r with Build_MemAttrHints _ f1 f2 => Build_MemAttrHints e f1 f2 end.
Notation "{[ r 'with' 'MemAttrHints_hints' := e ]}" :=
  match r with Build_MemAttrHints f0 _ f2 => Build_MemAttrHints f0 e f2 end.
Notation "{[ r 'with' 'MemAttrHints_transient' := e ]}" :=
  match r with Build_MemAttrHints f0 f1 _ => Build_MemAttrHints f0 f1 e end.

Inductive MemType := MemType_Normal | MemType_Device.
Scheme Equality for MemType.
#[export] Instance Decidable_eq_MemType :
forall (x y : MemType), Decidable (x = y) :=
Decidable_eq_from_dec MemType_eq_dec.

Inductive Shareability := Shareability_NSH | Shareability_ISH | Shareability_OSH.
Scheme Equality for Shareability.
#[export] Instance Decidable_eq_Shareability :
forall (x y : Shareability), Decidable (x = y) :=
Decidable_eq_from_dec Shareability_eq_dec.

Record MemoryAttributes  :=
  { MemoryAttributes_memtype : MemType;
    MemoryAttributes_device : DeviceType;
    MemoryAttributes_inner : MemAttrHints;
    MemoryAttributes_outer : MemAttrHints;
    MemoryAttributes_shareability : Shareability;
    MemoryAttributes_tagged : bool;
    MemoryAttributes_xs : bits 1; }.
Arguments MemoryAttributes : clear implicits.
Notation "{[ r 'with' 'MemoryAttributes_memtype' := e ]}" :=
  match r with Build_MemoryAttributes _ f1 f2 f3 f4 f5 f6 =>
    Build_MemoryAttributes e f1 f2 f3 f4 f5 f6 end.
Notation "{[ r 'with' 'MemoryAttributes_device' := e ]}" :=
  match r with Build_MemoryAttributes f0 _ f2 f3 f4 f5 f6 =>
    Build_MemoryAttributes f0 e f2 f3 f4 f5 f6 end.
Notation "{[ r 'with' 'MemoryAttributes_inner' := e ]}" :=
  match r with Build_MemoryAttributes f0 f1 _ f3 f4 f5 f6 =>
    Build_MemoryAttributes f0 f1 e f3 f4 f5 f6 end.
Notation "{[ r 'with' 'MemoryAttributes_outer' := e ]}" :=
  match r with Build_MemoryAttributes f0 f1 f2 _ f4 f5 f6 =>
    Build_MemoryAttributes f0 f1 f2 e f4 f5 f6 end.
Notation "{[ r 'with' 'MemoryAttributes_shareability' := e ]}" :=
  match r with Build_MemoryAttributes f0 f1 f2 f3 _ f5 f6 =>
    Build_MemoryAttributes f0 f1 f2 f3 e f5 f6 end.
Notation "{[ r 'with' 'MemoryAttributes_tagged' := e ]}" :=
  match r with Build_MemoryAttributes f0 f1 f2 f3 f4 _ f6 =>
    Build_MemoryAttributes f0 f1 f2 f3 f4 e f6 end.
Notation "{[ r 'with' 'MemoryAttributes_xs' := e ]}" :=
  match r with Build_MemoryAttributes f0 f1 f2 f3 f4 f5 _ =>
    Build_MemoryAttributes f0 f1 f2 f3 f4 f5 e end.

Inductive Regime := Regime_EL3 | Regime_EL30 | Regime_EL2 | Regime_EL20 | Regime_EL10.
Scheme Equality for Regime.
#[export] Instance Decidable_eq_Regime :
forall (x y : Regime), Decidable (x = y) :=
Decidable_eq_from_dec Regime_eq_dec.

Inductive TGx := TGx_4KB | TGx_16KB | TGx_64KB.
Scheme Equality for TGx.
#[export] Instance Decidable_eq_TGx :
forall (x y : TGx), Decidable (x = y) :=
Decidable_eq_from_dec TGx_eq_dec.

Record PhysMemRetStatus  :=
  { PhysMemRetStatus_statuscode : Fault;
    PhysMemRetStatus_extflag : bits 1;
    PhysMemRetStatus_errortype : bits 2;
    PhysMemRetStatus_store64bstatus : bits 64;
    PhysMemRetStatus_acctype : AccType; }.
Arguments PhysMemRetStatus : clear implicits.
Notation "{[ r 'with' 'PhysMemRetStatus_statuscode' := e ]}" :=
  match r with Build_PhysMemRetStatus _ f1 f2 f3 f4 => Build_PhysMemRetStatus e f1 f2 f3 f4 end.
Notation "{[ r 'with' 'PhysMemRetStatus_extflag' := e ]}" :=
  match r with Build_PhysMemRetStatus f0 _ f2 f3 f4 => Build_PhysMemRetStatus f0 e f2 f3 f4 end.
Notation "{[ r 'with' 'PhysMemRetStatus_errortype' := e ]}" :=
  match r with Build_PhysMemRetStatus f0 f1 _ f3 f4 => Build_PhysMemRetStatus f0 f1 e f3 f4 end.
Notation "{[ r 'with' 'PhysMemRetStatus_store64bstatus' := e ]}" :=
  match r with Build_PhysMemRetStatus f0 f1 f2 _ f4 => Build_PhysMemRetStatus f0 f1 f2 e f4 end.
Notation "{[ r 'with' 'PhysMemRetStatus_acctype' := e ]}" :=
  match r with Build_PhysMemRetStatus f0 f1 f2 f3 _ => Build_PhysMemRetStatus f0 f1 f2 f3 e end.

Record S1TTWParams  :=
  { S1TTWParams_ha : bits 1;
    S1TTWParams_hd : bits 1;
    S1TTWParams_tbi : bits 1;
    S1TTWParams_tbid : bits 1;
    S1TTWParams_nfd : bits 1;
    S1TTWParams_e0pd : bits 1;
    S1TTWParams_ds : bits 1;
    S1TTWParams_ps : bits 3;
    S1TTWParams_txsz : bits 6;
    S1TTWParams_epan : bits 1;
    S1TTWParams_dct : bits 1;
    S1TTWParams_nv1 : bits 1;
    S1TTWParams_cmow : bits 1;
    S1TTWParams_t0sz : bits 3;
    S1TTWParams_t1sz : bits 3;
    S1TTWParams_uwxn : bits 1;
    S1TTWParams_tgx : TGx;
    S1TTWParams_irgn : bits 2;
    S1TTWParams_orgn : bits 2;
    S1TTWParams_sh : bits 2;
    S1TTWParams_hpd : bits 1;
    S1TTWParams_ee : bits 1;
    S1TTWParams_wxn : bits 1;
    S1TTWParams_ntlsmd : bits 1;
    S1TTWParams_dc : bits 1;
    S1TTWParams_sif : bits 1;
    S1TTWParams_mair : bits 64; }.
Arguments S1TTWParams : clear implicits.
Notation "{[ r 'with' 'S1TTWParams_ha' := e ]}" :=
  match r with Build_S1TTWParams _ f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams e f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_hd' := e ]}" :=
  match r with Build_S1TTWParams f0 _ f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 e f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_tbi' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 _ f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 e f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_tbid' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 _ f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 e f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_nfd' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 _ f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 e f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_e0pd' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 _ f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 e f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_ds' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 _ f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 e f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_ps' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 _ f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 e f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_txsz' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 _ f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 e f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_epan' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 _ f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 e f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_dct' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 _ f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_nv1' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 _ f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 e f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_cmow' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _ f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 e f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_t0sz' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 _ f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 e f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_t1sz' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 _ f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_uwxn' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 _ f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 e f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_tgx' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 _ f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 e f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_irgn' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 _ f18 f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 e f18 f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_orgn' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 _ f19 f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 e f19 f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_sh' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 _ f20 f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 e f20 f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_hpd' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 _ f21 f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 e f21 f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_ee' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 _ f22 f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 e f22 f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_wxn' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 _ f23 f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 e f23 f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_ntlsmd' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 _ f24 f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 e f24 f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_dc' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 _ f25 f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 e f25 f26
      end.
Notation "{[ r 'with' 'S1TTWParams_sif' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 _ f26 =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 e f26
      end.
Notation "{[ r 'with' 'S1TTWParams_mair' := e ]}" :=
  match r with Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 _ =>
    Build_S1TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 e
      end.

Record S2TTWParams  :=
  { S2TTWParams_ha : bits 1;
    S2TTWParams_hd : bits 1;
    S2TTWParams_sl2 : bits 1;
    S2TTWParams_ds : bits 1;
    S2TTWParams_sw : bits 1;
    S2TTWParams_nsw : bits 1;
    S2TTWParams_sa : bits 1;
    S2TTWParams_nsa : bits 1;
    S2TTWParams_ps : bits 3;
    S2TTWParams_txsz : bits 6;
    S2TTWParams_fwb : bits 1;
    S2TTWParams_cmow : bits 1;
    S2TTWParams_s : bits 1;
    S2TTWParams_t0sz : bits 4;
    S2TTWParams_tgx : TGx;
    S2TTWParams_sl0 : bits 2;
    S2TTWParams_irgn : bits 2;
    S2TTWParams_orgn : bits 2;
    S2TTWParams_sh : bits 2;
    S2TTWParams_ee : bits 1;
    S2TTWParams_ptw : bits 1;
    S2TTWParams_vm : bits 1; }.
Arguments S2TTWParams : clear implicits.
Notation "{[ r 'with' 'S2TTWParams_ha' := e ]}" :=
  match r with Build_S2TTWParams _ f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 =>
    Build_S2TTWParams e f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_hd' := e ]}" :=
  match r with Build_S2TTWParams f0 _ f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 =>
    Build_S2TTWParams f0 e f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_sl2' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 _ f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 =>
    Build_S2TTWParams f0 f1 e f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_ds' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 _ f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 =>
    Build_S2TTWParams f0 f1 f2 e f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_sw' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 f3 _ f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 =>
    Build_S2TTWParams f0 f1 f2 f3 e f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_nsw' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 f3 f4 _ f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 =>
    Build_S2TTWParams f0 f1 f2 f3 f4 e f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_sa' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 f3 f4 f5 _ f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 =>
    Build_S2TTWParams f0 f1 f2 f3 f4 f5 e f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_nsa' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 _ f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 =>
    Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 e f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_ps' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 _ f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 =>
    Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 e f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_txsz' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 _ f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 =>
    Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 e f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_fwb' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 _ f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 =>
    Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_cmow' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 _ f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 =>
    Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 e f12 f13 f14 f15 f16 f17 f18 f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_s' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _ f13 f14 f15 f16 f17 f18 f19 f20 f21 =>
    Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 e f13 f14 f15 f16 f17 f18 f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_t0sz' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 _ f14 f15 f16 f17 f18 f19 f20 f21 =>
    Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 e f14 f15 f16 f17 f18 f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_tgx' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 _ f15 f16 f17 f18 f19 f20 f21 =>
    Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e f15 f16 f17 f18 f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_sl0' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 _ f16 f17 f18 f19 f20 f21 =>
    Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 e f16 f17 f18 f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_irgn' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 _ f17 f18 f19 f20 f21 =>
    Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 e f17 f18 f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_orgn' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 _ f18 f19 f20 f21 =>
    Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 e f18 f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_sh' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 _ f19 f20 f21 =>
    Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 e f19 f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_ee' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 _ f20 f21 =>
    Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 e f20 f21
      end.
Notation "{[ r 'with' 'S2TTWParams_ptw' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 _ f21 =>
    Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 e f21
      end.
Notation "{[ r 'with' 'S2TTWParams_vm' := e ]}" :=
  match r with Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 _ =>
    Build_S2TTWParams f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 e
      end.

Inductive CacheOp := CacheOp_Clean | CacheOp_Invalidate | CacheOp_CleanInvalidate.
Scheme Equality for CacheOp.
#[export] Instance Decidable_eq_CacheOp :
forall (x y : CacheOp), Decidable (x = y) :=
Decidable_eq_from_dec CacheOp_eq_dec.

Inductive CacheOpScope :=
  CacheOpScope_SetWay
  | CacheOpScope_PoU
  | CacheOpScope_PoC
  | CacheOpScope_PoP
  | CacheOpScope_PoDP
  | CacheOpScope_ALLU
  | CacheOpScope_ALLUIS.
Scheme Equality for CacheOpScope.
#[export] Instance Decidable_eq_CacheOpScope :
forall (x y : CacheOpScope), Decidable (x = y) :=
Decidable_eq_from_dec CacheOpScope_eq_dec.

Inductive CachePASpace :=
  CPAS_NonSecure
  | CPAS_Any
  | CPAS_RealmNonSecure
  | CPAS_Realm
  | CPAS_Root
  | CPAS_SecureNonSecure
  | CPAS_Secure.
Scheme Equality for CachePASpace.
#[export] Instance Decidable_eq_CachePASpace :
forall (x y : CachePASpace), Decidable (x = y) :=
Decidable_eq_from_dec CachePASpace_eq_dec.

Inductive CacheType := CacheType_Data | CacheType_Tag | CacheType_Data_Tag | CacheType_Instruction.
Scheme Equality for CacheType.
#[export] Instance Decidable_eq_CacheType :
forall (x y : CacheType), Decidable (x = y) :=
Decidable_eq_from_dec CacheType_eq_dec.

Record CacheRecord  :=
  { CacheRecord_acctype : AccType;
    CacheRecord_cacheop : CacheOp;
    CacheRecord_opscope : CacheOpScope;
    CacheRecord_cachetype : CacheType;
    CacheRecord_regval : bits 64;
    CacheRecord_paddress : FullAddress;
    CacheRecord_vaddress : bits 64;
    CacheRecord_set : Z;
    CacheRecord_way : Z;
    CacheRecord_level : Z;
    CacheRecord_shareability : Shareability;
    CacheRecord_translated : bool;
    CacheRecord_is_vmid_valid : bool;
    CacheRecord_vmid : bits 16;
    CacheRecord_is_asid_valid : bool;
    CacheRecord_asid : bits 16;
    CacheRecord_security : SecurityState;
    CacheRecord_cpas : CachePASpace; }.
Arguments CacheRecord : clear implicits.
Notation "{[ r 'with' 'CacheRecord_acctype' := e ]}" :=
  match r with Build_CacheRecord _ f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 =>
    Build_CacheRecord e f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 end.
Notation "{[ r 'with' 'CacheRecord_cacheop' := e ]}" :=
  match r with Build_CacheRecord f0 _ f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 =>
    Build_CacheRecord f0 e f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 end.
Notation "{[ r 'with' 'CacheRecord_opscope' := e ]}" :=
  match r with Build_CacheRecord f0 f1 _ f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 =>
    Build_CacheRecord f0 f1 e f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 end.
Notation "{[ r 'with' 'CacheRecord_cachetype' := e ]}" :=
  match r with Build_CacheRecord f0 f1 f2 _ f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 =>
    Build_CacheRecord f0 f1 f2 e f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 end.
Notation "{[ r 'with' 'CacheRecord_regval' := e ]}" :=
  match r with Build_CacheRecord f0 f1 f2 f3 _ f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 =>
    Build_CacheRecord f0 f1 f2 f3 e f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 end.
Notation "{[ r 'with' 'CacheRecord_paddress' := e ]}" :=
  match r with Build_CacheRecord f0 f1 f2 f3 f4 _ f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 =>
    Build_CacheRecord f0 f1 f2 f3 f4 e f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 end.
Notation "{[ r 'with' 'CacheRecord_vaddress' := e ]}" :=
  match r with Build_CacheRecord f0 f1 f2 f3 f4 f5 _ f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 =>
    Build_CacheRecord f0 f1 f2 f3 f4 f5 e f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 end.
Notation "{[ r 'with' 'CacheRecord_set' := e ]}" :=
  match r with Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 _ f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 =>
    Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 e f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 end.
Notation "{[ r 'with' 'CacheRecord_way' := e ]}" :=
  match r with Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 _ f9 f10 f11 f12 f13 f14 f15 f16 f17 =>
    Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 e f9 f10 f11 f12 f13 f14 f15 f16 f17 end.
Notation "{[ r 'with' 'CacheRecord_level' := e ]}" :=
  match r with Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 _ f10 f11 f12 f13 f14 f15 f16 f17 =>
    Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 e f10 f11 f12 f13 f14 f15 f16 f17 end.
Notation "{[ r 'with' 'CacheRecord_shareability' := e ]}" :=
  match r with Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 _ f11 f12 f13 f14 f15 f16 f17 =>
    Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e f11 f12 f13 f14 f15 f16 f17 end.
Notation "{[ r 'with' 'CacheRecord_translated' := e ]}" :=
  match r with Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 _ f12 f13 f14 f15 f16 f17 =>
    Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 e f12 f13 f14 f15 f16 f17 end.
Notation "{[ r 'with' 'CacheRecord_is_vmid_valid' := e ]}" :=
  match r with Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _ f13 f14 f15 f16 f17 =>
    Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 e f13 f14 f15 f16 f17 end.
Notation "{[ r 'with' 'CacheRecord_vmid' := e ]}" :=
  match r with Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 _ f14 f15 f16 f17 =>
    Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 e f14 f15 f16 f17 end.
Notation "{[ r 'with' 'CacheRecord_is_asid_valid' := e ]}" :=
  match r with Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 _ f15 f16 f17 =>
    Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e f15 f16 f17 end.
Notation "{[ r 'with' 'CacheRecord_asid' := e ]}" :=
  match r with Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 _ f16 f17 =>
    Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 e f16 f17 end.
Notation "{[ r 'with' 'CacheRecord_security' := e ]}" :=
  match r with Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 _ f17 =>
    Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 e f17 end.
Notation "{[ r 'with' 'CacheRecord_cpas' := e ]}" :=
  match r with Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 _ =>
    Build_CacheRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 e end.

Inductive TLBILevel := TLBILevel_Any | TLBILevel_Last.
Scheme Equality for TLBILevel.
#[export] Instance Decidable_eq_TLBILevel :
forall (x y : TLBILevel), Decidable (x = y) :=
Decidable_eq_from_dec TLBILevel_eq_dec.

Inductive TLBIMemAttr := TLBI_AllAttr | TLBI_ExcludeXS.
Scheme Equality for TLBIMemAttr.
#[export] Instance Decidable_eq_TLBIMemAttr :
forall (x y : TLBIMemAttr), Decidable (x = y) :=
Decidable_eq_from_dec TLBIMemAttr_eq_dec.

Inductive TLBIOp :=
  TLBIOp_DALL
  | TLBIOp_DASID
  | TLBIOp_DVA
  | TLBIOp_IALL
  | TLBIOp_IASID
  | TLBIOp_IVA
  | TLBIOp_ALL
  | TLBIOp_ASID
  | TLBIOp_IPAS2
  | TLBIOp_VAA
  | TLBIOp_VA
  | TLBIOp_VMALL
  | TLBIOp_VMALLS12
  | TLBIOp_RIPAS2
  | TLBIOp_RVAA
  | TLBIOp_RVA
  | TLBIOp_RPA
  | TLBIOp_PAALL.
Scheme Equality for TLBIOp.
#[export] Instance Decidable_eq_TLBIOp :
forall (x y : TLBIOp), Decidable (x = y) :=
Decidable_eq_from_dec TLBIOp_eq_dec.

Record TLBIRecord  :=
  { TLBIRecord_op : TLBIOp;
    TLBIRecord_from_aarch64 : bool;
    TLBIRecord_security : SecurityState;
    TLBIRecord_regime : Regime;
    TLBIRecord_vmid : bits 16;
    TLBIRecord_asid : bits 16;
    TLBIRecord_level : TLBILevel;
    TLBIRecord_attr : TLBIMemAttr;
    TLBIRecord_ipaspace : PASpace;
    TLBIRecord_address : bits 64;
    TLBIRecord_end_address_name : bits 64;
    TLBIRecord_tg : bits 2; }.
Arguments TLBIRecord : clear implicits.
Notation "{[ r 'with' 'TLBIRecord_op' := e ]}" :=
  match r with Build_TLBIRecord _ f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 =>
    Build_TLBIRecord e f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 end.
Notation "{[ r 'with' 'TLBIRecord_from_aarch64' := e ]}" :=
  match r with Build_TLBIRecord f0 _ f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 =>
    Build_TLBIRecord f0 e f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 end.
Notation "{[ r 'with' 'TLBIRecord_security' := e ]}" :=
  match r with Build_TLBIRecord f0 f1 _ f3 f4 f5 f6 f7 f8 f9 f10 f11 =>
    Build_TLBIRecord f0 f1 e f3 f4 f5 f6 f7 f8 f9 f10 f11 end.
Notation "{[ r 'with' 'TLBIRecord_regime' := e ]}" :=
  match r with Build_TLBIRecord f0 f1 f2 _ f4 f5 f6 f7 f8 f9 f10 f11 =>
    Build_TLBIRecord f0 f1 f2 e f4 f5 f6 f7 f8 f9 f10 f11 end.
Notation "{[ r 'with' 'TLBIRecord_vmid' := e ]}" :=
  match r with Build_TLBIRecord f0 f1 f2 f3 _ f5 f6 f7 f8 f9 f10 f11 =>
    Build_TLBIRecord f0 f1 f2 f3 e f5 f6 f7 f8 f9 f10 f11 end.
Notation "{[ r 'with' 'TLBIRecord_asid' := e ]}" :=
  match r with Build_TLBIRecord f0 f1 f2 f3 f4 _ f6 f7 f8 f9 f10 f11 =>
    Build_TLBIRecord f0 f1 f2 f3 f4 e f6 f7 f8 f9 f10 f11 end.
Notation "{[ r 'with' 'TLBIRecord_level' := e ]}" :=
  match r with Build_TLBIRecord f0 f1 f2 f3 f4 f5 _ f7 f8 f9 f10 f11 =>
    Build_TLBIRecord f0 f1 f2 f3 f4 f5 e f7 f8 f9 f10 f11 end.
Notation "{[ r 'with' 'TLBIRecord_attr' := e ]}" :=
  match r with Build_TLBIRecord f0 f1 f2 f3 f4 f5 f6 _ f8 f9 f10 f11 =>
    Build_TLBIRecord f0 f1 f2 f3 f4 f5 f6 e f8 f9 f10 f11 end.
Notation "{[ r 'with' 'TLBIRecord_ipaspace' := e ]}" :=
  match r with Build_TLBIRecord f0 f1 f2 f3 f4 f5 f6 f7 _ f9 f10 f11 =>
    Build_TLBIRecord f0 f1 f2 f3 f4 f5 f6 f7 e f9 f10 f11 end.
Notation "{[ r 'with' 'TLBIRecord_address' := e ]}" :=
  match r with Build_TLBIRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 _ f10 f11 =>
    Build_TLBIRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 e f10 f11 end.
Notation "{[ r 'with' 'TLBIRecord_end_address_name' := e ]}" :=
  match r with Build_TLBIRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 _ f11 =>
    Build_TLBIRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e f11 end.
Notation "{[ r 'with' 'TLBIRecord_tg' := e ]}" :=
  match r with Build_TLBIRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 _ =>
    Build_TLBIRecord f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 e end.

Inductive MBReqDomain :=
  MBReqDomain_Nonshareable
  | MBReqDomain_InnerShareable
  | MBReqDomain_OuterShareable
  | MBReqDomain_FullSystem.
Scheme Equality for MBReqDomain.
#[export] Instance Decidable_eq_MBReqDomain :
forall (x y : MBReqDomain), Decidable (x = y) :=
Decidable_eq_from_dec MBReqDomain_eq_dec.

Inductive MBReqTypes := MBReqTypes_Reads | MBReqTypes_Writes | MBReqTypes_All.
Scheme Equality for MBReqTypes.
#[export] Instance Decidable_eq_MBReqTypes :
forall (x y : MBReqTypes), Decidable (x = y) :=
Decidable_eq_from_dec MBReqTypes_eq_dec.

Inductive MemBarrierOp :=
  MemBarrierOp_DSB
  | MemBarrierOp_DMB
  | MemBarrierOp_ISB
  | MemBarrierOp_SSBB
  | MemBarrierOp_PSSBB
  | MemBarrierOp_SB.
Scheme Equality for MemBarrierOp.
#[export] Instance Decidable_eq_MemBarrierOp :
forall (x y : MemBarrierOp), Decidable (x = y) :=
Decidable_eq_from_dec MemBarrierOp_eq_dec.

Definition Level  : Type := {rangevar : Z & ArithFact ((-1 <=? rangevar) && (rangevar <=? 4))}.

Record TranslationInfo  :=
  { TranslationInfo_regime : Regime;
    TranslationInfo_vmid : option (bits 16);
    TranslationInfo_asid : option (bits 16);
    TranslationInfo_va : bits 64;
    TranslationInfo_s1level : option Level;
    TranslationInfo_s2info : option ((bits 64 * Level));
    TranslationInfo_s1params : option S1TTWParams;
    TranslationInfo_s2params : option S2TTWParams;
    TranslationInfo_memattr : MemoryAttributes; }.
Arguments TranslationInfo : clear implicits.
Notation "{[ r 'with' 'TranslationInfo_regime' := e ]}" :=
  match r with Build_TranslationInfo _ f1 f2 f3 f4 f5 f6 f7 f8 =>
    Build_TranslationInfo e f1 f2 f3 f4 f5 f6 f7 f8 end.
Notation "{[ r 'with' 'TranslationInfo_vmid' := e ]}" :=
  match r with Build_TranslationInfo f0 _ f2 f3 f4 f5 f6 f7 f8 =>
    Build_TranslationInfo f0 e f2 f3 f4 f5 f6 f7 f8 end.
Notation "{[ r 'with' 'TranslationInfo_asid' := e ]}" :=
  match r with Build_TranslationInfo f0 f1 _ f3 f4 f5 f6 f7 f8 =>
    Build_TranslationInfo f0 f1 e f3 f4 f5 f6 f7 f8 end.
Notation "{[ r 'with' 'TranslationInfo_va' := e ]}" :=
  match r with Build_TranslationInfo f0 f1 f2 _ f4 f5 f6 f7 f8 =>
    Build_TranslationInfo f0 f1 f2 e f4 f5 f6 f7 f8 end.
Notation "{[ r 'with' 'TranslationInfo_s1level' := e ]}" :=
  match r with Build_TranslationInfo f0 f1 f2 f3 _ f5 f6 f7 f8 =>
    Build_TranslationInfo f0 f1 f2 f3 e f5 f6 f7 f8 end.
Notation "{[ r 'with' 'TranslationInfo_s2info' := e ]}" :=
  match r with Build_TranslationInfo f0 f1 f2 f3 f4 _ f6 f7 f8 =>
    Build_TranslationInfo f0 f1 f2 f3 f4 e f6 f7 f8 end.
Notation "{[ r 'with' 'TranslationInfo_s1params' := e ]}" :=
  match r with Build_TranslationInfo f0 f1 f2 f3 f4 f5 _ f7 f8 =>
    Build_TranslationInfo f0 f1 f2 f3 f4 f5 e f7 f8 end.
Notation "{[ r 'with' 'TranslationInfo_s2params' := e ]}" :=
  match r with Build_TranslationInfo f0 f1 f2 f3 f4 f5 f6 _ f8 =>
    Build_TranslationInfo f0 f1 f2 f3 f4 f5 f6 e f8 end.
Notation "{[ r 'with' 'TranslationInfo_memattr' := e ]}" :=
  match r with Build_TranslationInfo f0 f1 f2 f3 f4 f5 f6 f7 _ =>
    Build_TranslationInfo f0 f1 f2 f3 f4 f5 f6 f7 e end.

Record DxB  := { DxB_domain : MBReqDomain; DxB_types : MBReqTypes; DxB_nXS : bool; }.
Arguments DxB : clear implicits.
Notation "{[ r 'with' 'DxB_domain' := e ]}" :=
  match r with Build_DxB _ f1 f2 => Build_DxB e f1 f2 end.
Notation "{[ r 'with' 'DxB_types' := e ]}" :=
  match r with Build_DxB f0 _ f2 => Build_DxB f0 e f2 end.
Notation "{[ r 'with' 'DxB_nXS' := e ]}" := match r with Build_DxB f0 f1 _ => Build_DxB f0 f1 e end.

Inductive Barrier  :=
  | Barrier_DSB : DxB -> Barrier
  | Barrier_DMB : DxB -> Barrier
  | Barrier_ISB : unit -> Barrier
  | Barrier_SSBB : unit -> Barrier
  | Barrier_PSSBB : unit -> Barrier
  | Barrier_SB : unit -> Barrier.
Arguments Barrier : clear implicits.

Record TLBI  := { TLBI_rec : TLBIRecord; TLBI_shareability : Shareability; }.
Arguments TLBI : clear implicits.
Notation "{[ r 'with' 'TLBI_rec' := e ]}" := match r with Build_TLBI _ f1 => Build_TLBI e f1 end.
Notation "{[ r 'with' 'TLBI_shareability' := e ]}" :=
  match r with Build_TLBI f0 _ => Build_TLBI f0 e end.

Record Exn  := { Exn_rec : ExceptionRecord; Exn_fault : option FaultRecord; }.
Arguments Exn : clear implicits.
Notation "{[ r 'with' 'Exn_rec' := e ]}" := match r with Build_Exn _ f1 => Build_Exn e f1 end.
Notation "{[ r 'with' 'Exn_fault' := e ]}" := match r with Build_Exn f0 _ => Build_Exn f0 e end.

Inductive arm_acc_type  :=
  | SAcc_STREAM : unit -> arm_acc_type
  | SAcc_VEC : bool -> arm_acc_type
  | SAcc_SVE : bool -> arm_acc_type
  | SAcc_SME : bool -> arm_acc_type
  | SAcc_UNPRIV : bool -> arm_acc_type
  | SAcc_A32LSMD : unit -> arm_acc_type
  | SAcc_ATOMICLS64 : unit -> arm_acc_type
  | SAcc_LIMITEDORDERED : unit -> arm_acc_type
  | SAcc_NONFAULT : unit -> arm_acc_type
  | SAcc_CNOTFIRST : unit -> arm_acc_type
  | SAcc_NV2REGISTER : unit -> arm_acc_type
  | SAcc_DC : unit -> arm_acc_type
  | SAcc_IC : unit -> arm_acc_type
  | SAcc_DCZVA : unit -> arm_acc_type
  | SAcc_ATPAN : unit -> arm_acc_type
  | SAcc_AT : unit -> arm_acc_type.
Arguments arm_acc_type : clear implicits.

Inductive register_value  :=
  | Regval_vector : list register_value -> register_value
  | Regval_list : list register_value -> register_value
  | Regval_option : option register_value -> register_value
  | Regval_bool : bool -> register_value
  | Regval_int : Z -> register_value
  | Regval_real : R -> register_value
  | Regval_string : string -> register_value
  | Regval_bit : bitU -> register_value.
Arguments register_value : clear implicits.

Definition regstate  : Type := unit.



Definition bit_of_regval (merge_var : register_value) : option bitU :=
   match merge_var with | Regval_bit v => Some v | _ => None end.

Definition regval_of_bit (v : bitU) : register_value := Regval_bit v.



Definition bool_of_regval (merge_var : register_value) : option bool :=
  match merge_var with | Regval_bool v => Some v | _ => None end.

Definition regval_of_bool (v : bool) : register_value := Regval_bool v.

Definition int_of_regval (merge_var : register_value) : option Z :=
  match merge_var with | Regval_int v => Some v | _ => None end.

Definition regval_of_int (v : Z) : register_value := Regval_int v.

Definition real_of_regval (merge_var : register_value) : option R :=
  match merge_var with | Regval_real v => Some v | _ => None end.

Definition regval_of_real (v : R) : register_value := Regval_real v.

Definition string_of_regval (merge_var : register_value) : option string :=
  match merge_var with | Regval_string v => Some v | _ => None end.

Definition regval_of_string (v : string) : register_value := Regval_string v.

Definition vector_of_regval {a} n (of_regval : register_value -> option a) (rv : register_value) : option (vec a n) := match rv with
  | Regval_vector v => if n =? length_list v then map_bind (vec_of_list n) (just_list (List.map of_regval v)) else None
  | _ => None
end.

Definition regval_of_vector {a size} (regval_of : a -> register_value) (xs : vec a size) : register_value := Regval_vector (List.map regval_of (list_of_vec xs)).

Definition list_of_regval {a} (of_regval : register_value -> option a) (rv : register_value) : option (list a) := match rv with
  | Regval_list v => just_list (List.map of_regval v)
  | _ => None
end.

Definition regval_of_list {a} (regval_of : a -> register_value) (xs : list a) : register_value := Regval_list (List.map regval_of xs).

Definition option_of_regval {a} (of_regval : register_value -> option a) (rv : register_value) : option (option a) := match rv with
  | Regval_option v => option_map of_regval v
  | _ => None
end.

Definition regval_of_option {a} (regval_of : a -> register_value) (v : option a) := Regval_option (option_map regval_of v).



Local Open Scope string.
Definition get_regval (reg_name : string) (s : regstate) : option register_value :=

  None.

Definition set_regval (reg_name : string) (v : register_value) (s : regstate) : option regstate :=

  None.

Definition register_accessors := (get_regval, set_regval).


Definition MR a r := monadR register_value a r unit.
Definition M a := monad register_value a unit.
Definition returnM {A:Type} := @returnm register_value A unit.
Definition returnR {A:Type} (R:Type) := @returnm register_value A (R + unit).
