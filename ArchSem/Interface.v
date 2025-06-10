(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zonguyan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
(*                                                                            *)
(*  All files except SailArmInstTypes.v are distributed under the             *)
(*  license below (BSD-2-Clause). The former is distributed                   *)
(*  under a mix of BSD-2-Clause and BSD-3-Clause Clear, as described          *)
(*  in the file header.                                                       *)
(*                                                                            *)
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

Require Import Strings.String.

Require Import ASCommon.Options.
Require Import ASCommon.Common.
Require Import ASCommon.FMon.

(** * The architecture requirements

The SailStdpp library already defines the architecure requirements, however this
development requires slightly more things, so this looks a bit different *)

(** The architecture parameters that must be provided to the interface *)
Module Type Arch.

  (** The type of registers, most likely string, but may be more fancy *)
  Parameter reg : Type.

  (** We need to implement a gmap indexed by registers *)
  Parameter reg_eq : EqDecision reg.
  #[export] Existing Instance reg_eq.
  Parameter reg_countable : @Countable reg reg_eq.
  #[export] Existing Instance reg_countable.

  (** Register value type are dependent on the register, therefore we need all
      the dependent type manipulation typeclasses *)
  Parameter reg_type : reg → Type.
  Parameter reg_type_eq : ∀ (r : reg), EqDecision (reg_type r).
  #[export] Existing Instance reg_type_eq.
  Parameter reg_type_countable : ∀ (r : reg), Countable (reg_type r).
  #[export] Existing Instance reg_type_countable.
  Parameter reg_type_inhabited : ∀ r : reg, Inhabited (reg_type r).
  #[export] Existing Instance reg_type_inhabited.
  Parameter ctrans_reg_type : CTrans reg_type.
  #[export] Existing Instance ctrans_reg_type.
  Parameter ctrans_reg_type_simpl : CTransSimpl reg_type.
  #[export] Existing Instance ctrans_reg_type_simpl.
  Parameter reg_type_eq_dep_dec : EqDepDecision reg_type.
  #[export] Existing Instance reg_type_eq_dep_dec.


  (** Register access kind (architecture specific) *)
  Parameter reg_acc : Type.

  Parameter reg_acc_eq : EqDecision reg_acc.
  #[export] Existing Instance reg_acc_eq.

  (** The program counter register *)
  Parameter pc_reg : reg.

  Parameter CHERI : bool.
  Parameter cap_size : N.

  Parameter addr_size : N.
  Parameter addr_space : Type.
  Parameter addr_space_eq : EqDecision addr_space.
  #[export] Existing Instance addr_space_eq.
  Parameter addr_space_countable : @Countable addr_space addr_space_eq.
  #[export] Existing Instance addr_space_countable.

  (** Memory access kind (architecture specific) *)
  Parameter mem_acc : Type.

  Parameter mem_acc_eq : EqDecision mem_acc.
  #[export] Existing Instance mem_acc_eq.

  (** Is this access an explicit access, e.g. whose access was explicitely
      required by the instruction. As minimima, this must be not an IFetch or a TTW
      access *)
  Parameter is_explicit : mem_acc → bool.
  (** Is this access an instruction fetch read *)
  Parameter is_ifetch : mem_acc → bool.
  (** Is this access a translation table walk *)
  Parameter is_ttw : mem_acc → bool.

  (** All the access type classifiers below are for explicit accesses.
      Therefore, they must all imply [is_explicit] *)

  (** Is this access relaxed, aka. no acquire or release strength *)
  Parameter is_relaxed : mem_acc → bool.
  (** Is this an acquire or a release access (Depending on whether this is a
      read or write *)
  Parameter is_rel_acq : mem_acc → bool.
  (** Is this a weak PC acquire (not ordered after write release *)
  Parameter is_acq_rcpc : mem_acc → bool.
  (** Is this a standalone access, aka. not part of an exclusive or RMW pair.
      This is based on the access type, so an unmatched exclusive load would not be
      "standalone" *)
  Parameter is_standalone : mem_acc → bool.
  (** Is this an exclusive access *)
  Parameter is_exclusive : mem_acc → bool.
  (** Is this part of an RMW instruction. Another RMW access to the same address
      in the same instruction is expected *)
  Parameter is_atomic_rmw : mem_acc → bool.

  (** Abort description. This represent physical memory aborts on memory
      accesses, for example when trying to access outside of physical memory
      range. Those aborts are generated by the model*)
  Parameter abort : Type.

  (** Barrier types *)
  Parameter barrier : Type.

  Parameter barrier_eq : EqDecision barrier.
  #[export] Existing Instance barrier_eq.


  (** Cache operations (data and instruction caches) *)
  Parameter cache_op : Type.

  Parameter cache_op_eq : EqDecision cache_op.
  #[export] Existing Instance cache_op_eq.

  (** TLB operations *)
  Parameter tlb_op : Type.

  Parameter tlb_op_eq : EqDecision tlb_op.
  #[export] Existing Instance tlb_op_eq.

  (** Fault type for a architectural fault or exception *)
  Parameter fault : Type.

  Parameter fault_eq : EqDecision fault.
  #[export] Existing Instance fault_eq.

  (** Payload for a translation start outcome. This should contain at least TLB
      indexing information, in particular the VA *)
  Parameter trans_start : Type.

  Parameter trans_start_eq : EqDecision trans_start.
  #[export] Existing Instance trans_start_eq.

  (** Payload for a translation end outcome. This should contain at least the
      output physical address (matching with the address field of memory
      outcomes) *)
  Parameter trans_end : Type.

  Parameter trans_end_eq : EqDecision trans_end.
  #[export] Existing Instance trans_end_eq.

End Arch.

(** * The Interface *)

Module Interface (A : Arch).
  Import A.
  #[local] Open Scope N.

  (** ** Memory utility *)
  (** Virtual address are tag-less bitvectors *)
  Definition address := bv addr_size.
  #[export] Typeclasses Transparent address.
  #[export] Hint Transparent address : bv_unfold_db.

  Definition addr_addN (addr : address) n := (addr `+Z` (Z.of_N n))%bv.
  Lemma addr_addN_assoc addr n n':
    addr_addN (addr_addN addr n) n' = addr_addN addr (n + n').
  Proof. unfold addr_addN. bv_solve. Qed.
  #[export] Hint Rewrite addr_addN_assoc : addr.
  Lemma addr_addN_zero addr : addr_addN addr 0 = addr.
  Proof. unfold addr_addN. bv_solve. Qed.
  #[export] Hint Rewrite addr_addN_zero : addr.

  (* If faced with [addr_addN pa n = addr_addN pa n'], trying to prove [n = n']
     is often a very good idea *)
  Definition f_equal_addr_addN addr := f_equal (addr_addN addr).
  Hint Resolve f_equal_addr_addN : addr.

  (** The list of all physical addresses accessed when accessing [pa] with size
      [n] *)
  Definition addr_range addr n := seqN 0 n |> map (λ n, addr_addN addr n).

  Lemma addr_range_length addr n : length (addr_range addr n) = N.to_nat n.
  Proof. unfold addr_range. by autorewrite with list. Qed.

  Definition addr_in_range (addr : address) size (addr' : address) : Prop :=
    let diff := Z.to_N $ bv_unsigned (addr' - addr) in
    (diff < size)%N.
  #[export] Instance addr_in_range_dec addr size addr' :
    Decision (addr_in_range addr size addr').
  Proof. unfold addr_in_range. tc_solve. Defined.

  Lemma addr_in_range_spec addr size addr':
    addr_in_range addr size addr' ↔ ∃ n, addr_addN addr n = addr' ∧ n < size.
  Proof.
    unfold addr_in_range, is_Some.
    split.
    - intro H.
      unfold addr_addN.
      eexists; split; try eassumption; clear H.
      bv_solve.
    - cdestruct addr' |- ?.
      unfold addr_addN in *.
      rewrite N2Z.inj_lt.
      bv_simplify_arith.
      eapply Z.le_lt_trans.
      + apply Z.mod_le; bv_solve.
      + lia.
  Qed.

  Definition addr_overlap addr1 size1 addr2 size2 : Prop :=
    addr_in_range addr1 size1 addr2 ∨ addr_in_range addr2 size2 addr1.
  #[export] Typeclasses Transparent addr_overlap.

  Lemma addr_overlap_spec addr1 size1 addr2 size2 :
    addr_overlap addr1 size1 addr2 size2 ∧ 0 < size1 ∧ 0 < size2 ↔
      ∃ n1 n2, (n1 < size1 ∧ n2 < size2 ∧ addr_addN addr1 n1 = addr_addN addr2 n2)%N.
  Proof.
    unfold addr_overlap.
    setoid_rewrite addr_in_range_spec.
    split.
    - cdestruct addr1,addr2 |- ? # CDestrSplitGoal;
        setoid_rewrite addr_addN_assoc;
        typeclasses eauto with core lia addr.
    - cdestruct |- *** as n1 n2 H1 H2 H #CDestrSplitGoal.
      all: try lia.
      destruct decide (n1 ≤ n2).
      (* TODO improve automation here *)
      1: right; exists (n2 - n1).
      2: left; exists (n1 - n2).
      all: split; try lia.
      all: unfold addr_addN in *.
      all: rewrite N2Z.inj_sub by lia.
      all: rewrite bv_add_Z_add_l.
      all: (rewrite H || rewrite <- H); clear H.
      all: bv_solve.
  Qed.

  Lemma addr_overlap_refl addr size :
    0 < size → addr_overlap addr size addr size.
  Proof.
    unfold addr_overlap. left.
    apply addr_in_range_spec.
    eexists.
    by rewrite addr_addN_zero.
  Qed.
  Hint Resolve addr_overlap_refl : addr.

  Lemma addr_overlap_sym addr1 size1 addr2 size2 :
    addr_overlap addr1 size1 addr2 size2 → addr_overlap addr2 size2 addr1 size1.
  Proof. unfold addr_overlap. tauto. Qed.
  Hint Immediate addr_overlap_sym : addr.

  Lemma addr_overlap_sym_iff addr1 size1 addr2 size2 :
    addr_overlap addr1 size1 addr2 size2 ↔ addr_overlap addr2 size2 addr1 size1.
  Proof. unfold addr_overlap. tauto. Qed.

  (** ** Memory read request *)
  Module ReadReq.
    #[local] Open Scope N.
    Record t {n : N} {nt : N} :=
      make
        { access_kind : mem_acc;
          address : address;
          address_space : addr_space;
        }.
    Arguments t : clear implicits.

    #[global] Instance eq_dec n nt : EqDecision (t n nt).
    Proof. solve_decision. Defined.

    #[global] Instance jmeq_dec : EqDep2Decision t.
    Proof. intros ? ? ? ? ? ? [] []. decide_jmeq. Defined.

    Definition range `(rr : t n nt) := addr_range (address rr) n.
  End ReadReq.

  (** ** Memory write request *)
  Module WriteReq.
    #[local] Open Scope N.
    Record t {n : N} {nt : N} :=
      make
        { access_kind : mem_acc;
          address : address;
          address_space : addr_space;
          value : bv (8 * n);
          tags : bv nt;
        }.
    Arguments t : clear implicits.

    #[global] Instance eq_dec n nt : EqDecision (t n nt).
    Proof. solve_decision. Defined.

    #[global] Instance jmeq_dec : EqDep2Decision t.
    Proof. intros ? ? ? ? ? ? [] []. decide_jmeq. Defined.

    Definition range `(wr : t n nt) := addr_range (address wr) n.
  End WriteReq.


  (** ** Outcomes *)

  (** The effect type used by ISA models *)
  Inductive outcome : eff :=
    (** Reads a register [reg] with provided access type [racc]. It is up to
        concurrency model to interpret [racc] properly *)
  | RegRead (reg : reg) (racc : reg_acc)

    (** Write a register [reg] with value [reg_val] and access type [racc]. *)
  | RegWrite (reg : reg) (racc : reg_acc) (regval: reg_type reg)

    (** Read [n] bytes of memory in a single access (Single Copy Atomic in Arm
        terminology). See [ReadReq.t] for the various required fields.

        The result is either a success (value read and optional tag) or a
        error (intended for physical memory errors, not translation, access
        control, or segmentation faults *)
  | MemRead (n : N) (nt : N) (rr: ReadReq.t n nt)

    (** Announce the address or a subsequent write, all the parameters must
        match up with the content of the later write *)
  | MemWriteAddrAnnounce (n : N) (nt : N) (addr : address)
      (acc : mem_acc) (pas : addr_space)

    (** Write [n] bytes of memory in a single access (Single Copy Atomic in
        Arm terminology). See [WriteReq.t] for the various required fields.

        If the result is:
        - inl true: The write happened
        - inl false: The write didn't happened because the required strength
          could not be achieved (e.g. exclusive failure)
        - inr abort: The write was attempted, but a physical abort happened
          *)
  | MemWrite (n : N) (nt : N) (wr : WriteReq.t n nt)

    (** Issues a barrier such as DMB (for Arm), fence.XX (for RISC-V), ... *)
  | Barrier (b : barrier)
    (** Issues a cache operation such as DC or IC (for Arm) *)
  | CacheOp (cop : cache_op)
    (** Issues a TLB maintenance operation, such as TLBI (for Arm) *)
  | TlbOp (tlbop : tlb_op)
    (** Take an exception. Includes hardware faults and physical interrupts *)
  | TakeException (flt : fault)
    (** Return from an exception to this address e.g. ERET (for Arm) or
        IRET (for x86) *)
  | ReturnException
    (** Start a translation. In operational model this would start a TLB lookup *)
  | TranslationStart (ts : trans_start)
    (** End a translation and give the PA *)
  | TranslationEnd (te : trans_end)

    (** Bail out when something went wrong. This is to represent ISA model
        incompleteness: When getting out of the range of supported
        instructions or behaviors of the ISA model. The string is for
        debugging but otherwise irrelevant *)
  | GenericFail (msg : string).

  #[export] Instance outcome_ret : Effect outcome :=
    λ out, match out with
            | RegRead r _ => reg_type r
            | MemRead n nt _ =>
                result abort (bv (8 * n) * bv nt)%type
            | MemWrite _ _ _ => (result abort ())%type
            | GenericFail _ => ∅%type
            | _ => unit
            end.

  #[export] Instance outcome_wf : EffWf outcome.
  Proof using. intros []; cbn; try tc_solve. Defined.


  (* Automatically implies EqDecision (outcome T) on any T *)
  #[export] Instance outcome_eq_dec : EqDecision outcome.
  Proof using. intros [] []; decide_eq. Defined.

  #[export] Instance outcome_EffCTrans : EffCTrans outcome.
  Proof using.
    intros [] [].
    all: try discriminate.
    all: cbn in *.
    all: try (intros; assumption).
    (* There is 2 non trivial cases where the return type depends on the content
       of the effect constructor *)
    - (* RegRead case *)
      intros e. eapply ctrans. abstract naive_solver.
    - (* MemRead case *)
      intros eq [[data tags]| ?]; [left | right]; intuition.
      + refine (ctrans _ data). abstract (inversion eq; f_equal; done).
      + refine (ctrans _ tags). abstract (inversion eq; f_equal; done).
  Defined.

  #[export] Instance outcome_EffCTransSimpl : EffCTransSimpl outcome.
  Proof.
    intros [] ? ?; try reflexivity; cbn;
      repeat case_match; simp ctrans; reflexivity.
  Qed.

  (** ** Instruction monad *)

  (** An instruction semantic is a non-deterministic program using the
      uninterpreted effect type [outcome] *)
  Definition iMon := cMon outcome.
  #[global] Typeclasses Transparent iMon.

  (** A single event in an instruction execution. Events cannot contain
      termination outcome (outcomes of type `outcome False`) *)
  Definition iEvent := fEvent outcome.
  #[global] Typeclasses Transparent iEvent.

  (** An execution trace for a single instruction. *)
  Definition iTrace := fTrace outcome.
  #[global] Typeclasses Transparent iTrace.

  (** * Event accessors

     A set of accessors over the iEvent type *)

  (** Get the register out of a register event *)
  Definition get_reg (ev : iEvent) : option reg :=
    match ev with
    | RegRead reg _ &→ _ => Some reg
    | RegWrite reg _ _ &→ _ => Some reg
    | _ => None
    end.

  (** Get a register and its value out of a register event

      This gives both the register and the value, because later the value might
      have a type that depend on the register *)
  Definition get_reg_val (ev : iEvent) : option (sigT reg_type) :=
    match ev with
    | RegRead reg _ &→ regval => Some (existT reg regval)
    | RegWrite reg _ regval &→ _ => Some (existT reg regval)
    | _ => None
    end.

  Lemma get_reg_val_get_reg (ev : iEvent) rrv :
    get_reg_val ev = Some rrv → get_reg ev = Some rrv.T1.
  Proof. destruct ev as [[] ?]; cbn; hauto lq:on. Qed.

  Definition get_rec_acc (ev : iEvent) : option reg_acc :=
    match ev with
    | RegRead _ racc &→ _ => Some racc
    | RegWrite _ racc _ &→ _ => Some racc
    | _ => None
    end.

  (** Get the physical address out of an memory event *)
  Definition get_addr (e : iEvent) : option address:=
    match e with
    | MemRead _ _ rr &→ _ => Some rr.(ReadReq.address)
    | MemWriteAddrAnnounce _ _ addr _ _ &→ _ => Some addr
    | MemWrite _ _ wr &→ _ => Some wr.(WriteReq.address)
    | _ => None
    end.

  Definition get_addr_space (ev : iEvent) : option addr_space :=
    match ev with
    | MemRead _ _ rr &→ _ => Some rr.(ReadReq.address_space)
    | MemWriteAddrAnnounce _ _ _ _ pas &→ _ => Some pas
    | MemWrite _ _ wr &→ _ => Some wr.(WriteReq.address_space)
    | _ => None
    end.

  (** Get the size out of an memory event *)
  Definition get_size (ev : iEvent) : option N :=
    match ev with
    | MemRead n nt _ &→ _ => Some n
    | MemWriteAddrAnnounce n _ _ _ _ &→ _ => Some n
    | MemWrite n _ _ &→ _ => Some n
    | _ => None
    end.

  (** Get the value out of a memory event *)
  Definition get_mem_value (ev : iEvent) : option bvn :=
    match ev with
    | MemRead n _ _ &→ Ok (bv, _) => Some (bv : bvn)
    | MemWrite n _ wr &→ _ => Some (wr.(WriteReq.value) : bvn)
    | _ => None
    end.

  Lemma get_mem_value_size (ev : iEvent) bv :
    get_mem_value ev = Some bv → get_size ev = Some (bvn_n bv / 8)%N.
  Proof.
    destruct ev as [[] ?];
      cdestruct bv |- ** #CDestrMatch; cbn; f_equal; lia.
  Qed.

  Definition get_access_kind (ev : iEvent) : option mem_acc :=
    match ev with
    | MemRead _ _ rr &→ _ => Some rr.(ReadReq.access_kind)
    | MemWrite _ _ wr &→ _ => Some wr.(WriteReq.access_kind)
    | _ => None
    end.


  (** Get the content of a barrier, returns none if not a barrier (or is an
        invalid EID) *)
  Definition get_barrier (ev : iEvent) : option barrier:=
    match ev with
    | Barrier b &→ () => Some b
    | _ => None
    end.

  (** Get the content of a cache operation, returns none if not a cache operation
        (or is an invalid EID) *)
  Definition get_cacheop (ev : iEvent) : option cache_op :=
    match ev with
    | CacheOp co &→ () => Some co
    | _ => None
    end.

  (** Get the content of a TLB operation, returns none if not a TLB operation
        (or is an invalid EID) *)
  Definition get_tlbop (ev : iEvent) : option tlb_op :=
    match ev with
    | TlbOp to &→ () => Some to
    | _ => None
    end.

  Definition get_fault (ev : iEvent) : option fault :=
    match ev with
    | TakeException flt &→ () => Some flt
    | _ => None
    end.

  Definition get_trans_start (ev : iEvent) : option trans_start :=
    match ev with
    | TranslationStart ts &→ () => Some ts
    | _ => None
    end.

  Definition get_trans_end (ev : iEvent) : option trans_end :=
    match ev with
    | TranslationEnd te &→ () => Some te
    | _ => None
    end.


  (** * Event manipulation

     This is a set of helper function to manipulate events *)


  (** ** Register reads ***)

  Section isReg.
    Context (P : ∀ r : reg, reg_acc → reg_type r → Prop).
    Implicit Type ev : iEvent.

    Definition is_reg_readP ev : Prop :=
      match ev with
      | RegRead reg racc &→ rval => P reg racc rval
      | _ => False
      end.
    #[export] Typeclasses Opaque is_reg_readP.
    Definition is_reg_readP_spec ev :
      is_reg_readP ev ↔
        ∃ reg racc rval, ev = RegRead reg racc &→ rval ∧ P reg racc rval.
    Proof. destruct ev as [[] ?]; split; cdestruct |- **;naive_solver. Qed.
    Definition is_reg_readP_cdestr ev := cdestr_simpl false (is_reg_readP_spec ev).
    #[global] Existing Instance is_reg_readP_cdestr.

    Context `{Pdec: ∀ reg racc rval, Decision (P reg racc rval)}.
    #[global] Instance is_reg_readP_dec ev: Decision (is_reg_readP ev).
    Proof using Pdec. destruct ev as [[] ?]; cbn in *; tc_solve. Defined.

    (** ** Register writes *)
    Definition is_reg_writeP ev : Prop :=
      match ev with
      | RegWrite reg racc rval &→ _ => P reg racc rval
      | _ => False
      end.

    Definition is_reg_writeP_spec ev :
      is_reg_writeP ev ↔
        ∃ reg racc rval,
          ev = RegWrite reg racc rval &→ () ∧ P reg racc rval.
    Proof.
      destruct ev as [[] fret];
        split; cdestruct |- ?; destruct fret; naive_solver.
    Qed.
    Definition is_reg_writeP_cdestr ev := cdestr_simpl false (is_reg_writeP_spec ev).
    #[global] Existing Instance is_reg_writeP_cdestr.

    #[global] Instance is_reg_writeP_dec ev: Decision (is_reg_writeP ev).
    Proof using Pdec. destruct ev as [[] ?]; cbn in *; tc_solve. Defined.

  End isReg.
  Notation is_reg_read := (is_reg_readP (λ _ _ _, True)).
  Notation is_reg_write := (is_reg_writeP (λ _ _ _, True)).

  (** ** Memory reads *)

  (** *** Memory reads request

      This is the general case for both failed and successful memory reads *)
  Section isMemReadReq.
    Context
    (P : ∀ n nt : N, ReadReq.t n nt → (result abort (bv (8 * n) * bv nt)) → Prop).
    Implicit Type ev : iEvent.

    Definition is_mem_read_reqP ev : Prop :=
      match ev with
      | MemRead n nt rr &→ rres => P n nt rr rres
      | _ => False
      end.
    #[export] Typeclasses Opaque is_mem_read_reqP.

    Definition is_mem_read_reqP_spec ev:
      is_mem_read_reqP ev ↔
        ∃ n nt rr rres, ev = MemRead n nt rr &→ rres ∧ P n nt rr rres.
    Proof. destruct ev as [[] ?]; split; cdestruct |- ?; naive_solver. Qed.
    Definition is_mem_read_reqP_cdestr ev := cdestr_simpl false (is_mem_read_reqP_spec ev).
    #[global] Existing Instance is_mem_read_reqP_cdestr.

    Context `{Pdec : ∀ n nt rr rres, Decision (P n nt rr rres)}.
    #[global] Instance is_mem_read_reqP_dec ev : Decision (is_mem_read_reqP ev).
    Proof using Pdec. destruct ev as [[] ?]; cbn in *; tc_solve. Defined.
  End isMemReadReq.
  Notation is_mem_read_req := (is_mem_read_reqP (λ _ _ _ _, True)).

  (** *** Successful memory reads *)
  Section IsMemRead.
    Context (P : ∀ n nt : N, ReadReq.t n nt → bv (8 * n) → bv nt → Prop).
    Implicit Type ev : iEvent.

    (** Filters memory read that are successful (that did not get a physical
        memory abort *)
    Definition is_mem_readP ev : Prop :=
      is_mem_read_reqP (λ n nt rr rres,
          match rres with
          | Ok (rval, tags) => P n nt rr rval tags
          | _ => False end) ev.
    #[export] Typeclasses Opaque is_mem_readP.

    Definition is_mem_readP_spec ev:
      is_mem_readP ev ↔
        ∃ n nt rr rval tags,
          ev = MemRead n nt rr &→ Ok (rval, tags) ∧ P n nt rr rval tags.
    Proof. unfold is_mem_readP. rewrite is_mem_read_reqP_spec. hauto l:on. Qed.
    Definition is_mem_readP_cdestr ev := cdestr_simpl false (is_mem_readP_spec ev).
    #[global] Existing Instance is_mem_readP_cdestr.

    Context `{Pdec: ∀ n nt rr rval otag, Decision (P n nt rr rval otag)}.
    #[global] Instance is_mem_readP_dec ev: Decision (is_mem_readP ev).
    Proof using Pdec. unfold is_mem_readP. solve_decision. Defined.
  End IsMemRead.
  Notation is_mem_read := (is_mem_readP (λ _ _ _ _ _, True)).

  (** ** Memory writes *)

  (** *** Memory write address announce *)
  Section isMemWriteAddrAnnounce.
    Context
      (P : N → N → address → mem_acc → addr_space → Prop).
    Implicit Type ev : iEvent.

    Definition is_mem_write_addr_announceP ev : Prop :=
      match ev with
      | MemWriteAddrAnnounce n nt addr acc pas &→ () => P n nt addr acc pas
      | _ => False
      end.

    Definition is_mem_write_addr_announceP_spec ev:
      is_mem_write_addr_announceP ev ↔
        ∃ n nt addr acc pas,
          ev = MemWriteAddrAnnounce n nt addr acc pas &→ () ∧ P n nt addr acc pas.
    Proof.
      destruct ev as [[] fret];
        split; cdestruct |- ?; destruct fret; naive_solver.
    Qed.
    Typeclasses Opaque is_mem_write_addr_announceP.
    Definition is_mem_write_addr_announceP_cdestr ev :=
      cdestr_simpl false (is_mem_write_addr_announceP_spec ev).
    #[global] Existing Instance is_mem_write_addr_announceP_cdestr.

    Context `{Pdec: ∀ n nt addr acc pas, Decision (P n nt addr acc pas)}.
    #[global] Instance is_mem_write_addr_announceP_dec ev:
      Decision (is_mem_write_addr_announceP ev).
    Proof using Pdec. destruct ev as [[] ?]; cbn in *; tc_solve. Defined.
  End isMemWriteAddrAnnounce.
  Notation is_mem_write_addr_announce :=
    (is_mem_write_addr_announceP (λ _ _ _ _ _, True)).


  (** *** Memory write requests

      This is the general case for both failed and successful memory writes. *)
  Section isMemWriteReq.
    Context
      (P : ∀ n nt : N, WriteReq.t n nt → (result abort ()) → Prop).
    Implicit Type ev : iEvent.

    Definition is_mem_write_reqP ev : Prop :=
      match ev with
      | MemWrite n nt wr &→ wres => P n nt wr wres
      | _ => False
      end.
    Typeclasses Opaque is_mem_write_reqP.

    Definition is_mem_write_reqP_spec ev:
      is_mem_write_reqP ev ↔
        ∃ n nt wr wres, ev = MemWrite n nt wr &→ wres ∧ P n nt wr wres.
    Proof. destruct ev as [[] ?]; split; cdestruct |- ?; naive_solver. Qed.
    Definition is_mem_write_reqP_cdestr ev := cdestr_simpl false (is_mem_write_reqP_spec ev).
    #[global] Existing Instance is_mem_write_reqP_cdestr.

    Context `{Pdec: ∀ n nt wr wres, Decision (P n nt wr wres)}.
    #[global] Instance is_mem_write_reqP_dec ev: Decision (is_mem_write_reqP ev).
    Proof using Pdec. destruct ev as [[] ?]; cbn in *; tc_solve. Defined.
  End isMemWriteReq.
  Notation is_mem_write_req := (is_mem_write_reqP (λ _ _ _ _, True)).


  (** *** Successful memory writes *)
  Section isMemWrite.
    Context
      (P : ∀ n nt : N, WriteReq.t n nt → Prop).
    Implicit Type ev : iEvent.

    (** Filters memory writes that are successful (that did not get a physical
        memory abort, or an exclusive failure).*)
    Definition is_mem_writeP ev: Prop :=
      is_mem_write_reqP (λ n nt wr wres,
          match wres with
          | Ok () => P n nt wr
          | _ => False end) ev.
    Typeclasses Opaque is_mem_writeP.

    Definition is_mem_writeP_spec ev:
      is_mem_writeP ev ↔
        ∃ n nt wr, ev = MemWrite n nt wr &→ Ok () ∧ P n nt wr.
    Proof. unfold is_mem_writeP. rewrite is_mem_write_reqP_spec. hauto l:on. Qed.
    Definition is_mem_writeP_cdestr ev := cdestr_simpl false (is_mem_writeP_spec ev).
    #[global] Existing Instance is_mem_writeP_cdestr.

    Context `{Pdec: ∀ n nt wr, Decision (P n nt wr)}.
    #[global] Instance is_mem_writeP_dec ev: Decision (is_mem_writeP ev).
    Proof using Pdec. unfold is_mem_writeP. solve_decision. Defined.
  End isMemWrite.
  Notation is_mem_write := (is_mem_writeP (λ _ _ _, True)).

  Definition is_mem_event (ev : iEvent) :=
    is_mem_read ev \/ is_mem_write ev.
  #[global] Typeclasses Transparent is_mem_event.

  (** ** Allow filtering memory events by kind more easily *)
  Section MemEventByKind.
    Context (P : mem_acc → Prop).
    Context {Pdec : ∀ acc, Decision (P acc)}.
    Implicit Type ev : iEvent.

    Definition is_mem_read_kindP :=
      is_mem_readP (λ _ _ rr _ _, P rr.(ReadReq.access_kind)).
    #[global] Typeclasses Transparent is_mem_read_kindP.
    Definition is_mem_write_kindP :=
      is_mem_writeP (λ _ _ wr, P wr.(WriteReq.access_kind)).
    #[global] Typeclasses Transparent is_mem_write_kindP.

    Definition is_mem_event_kindP (ev : iEvent) :=
      if get_access_kind ev is Some acc then P acc else False.
    #[global] Instance is_mem_event_kindP_dec ev:
      Decision (is_mem_event_kindP ev).
    Proof using Pdec. unfold is_mem_event_kindP. tc_solve. Defined.
  End MemEventByKind.

  (** ** Barriers *)
  Section isBarrier.
    Context (P : barrier → Prop).
    Implicit Type ev : iEvent.

    Definition is_barrierP ev: Prop :=
      if ev is Barrier b &→ _ then P b else False.
    Typeclasses Opaque is_barrierP.

    Definition is_barrierP_spec ev:
      is_barrierP ev ↔ ∃ barrier, ev = Barrier barrier &→ () ∧ P barrier.
    Proof.
      destruct ev as [[] fret];
        split; cdestruct |- ?; destruct fret; naive_solver.
    Qed.

    Context `{Pdec: ∀ b, Decision (P b)}.
    #[global] Instance is_barrierP_dec ev: Decision (is_barrierP ev).
    Proof using Pdec. unfold_decide. Defined.
  End isBarrier.
  Notation is_barrier := (is_barrierP (λ _, True)).

  (** ** CacheOp *)
  Section isCacheop.
    Context (P : cache_op → Prop).
    Implicit Type ev : iEvent.

    Definition is_cacheopP ev: Prop :=
      if ev is CacheOp c &→ _ then P c else False.
    Typeclasses Opaque is_cacheopP.

    Definition is_cacheopP_spec ev:
      is_cacheopP ev ↔ ∃ cacheop, ev = CacheOp cacheop &→ () ∧ P cacheop.
    Proof.
      destruct ev as [[] fret];
        split; cdestruct |- ?; destruct fret; naive_solver.
    Qed.

    Context `{Pdec: ∀ c, Decision (P c)}.
    #[global] Instance is_cacheopP_dec ev: Decision (is_cacheopP ev).
    Proof using Pdec. unfold_decide. Defined.
  End isCacheop.
  Notation is_cacheop := (is_cacheopP (λ _, True)).

  (** ** Tlbop *)
  Section isTlbop.
    Context (P : tlb_op → Prop).
    Implicit Type ev : iEvent.

    Definition is_tlbopP ev: Prop :=
      if ev is TlbOp c &→ _ then P c else False.
    Typeclasses Opaque is_tlbopP.

    Definition is_tlbopP_spec ev:
      is_tlbopP ev ↔ ∃ tlbop, ev = TlbOp tlbop &→ () ∧ P tlbop.
    Proof.
      destruct ev as [[] fret];
        split; cdestruct |- ?; destruct fret; naive_solver.
    Qed.

    Context `{Pdec: ∀ c, Decision (P c)}.
    #[global] Instance is_tlbopP_dec ev: Decision (is_tlbopP ev).
    Proof using Pdec. unfold is_tlbopP. solve_decision. Defined.
  End isTlbop.
  Notation is_tlbop := (is_tlbopP (λ _, True)).

  Section isTakeException.
    Context (P : fault → Prop).
    Implicit Type ev : iEvent.

    Definition is_take_exceptionP ev: Prop :=
      if ev is TakeException c &→ _ then P c else False.
    Typeclasses Opaque is_take_exceptionP.

    Definition is_take_exceptionP_spec ev:
      is_take_exceptionP ev ↔ ∃ take_exception, ev = TakeException take_exception &→ () ∧ P take_exception.
    Proof.
      destruct ev as [[] fret];
        split; cdestruct |- ?; destruct fret; naive_solver.
    Qed.

    Context `{Pdec: ∀ c, Decision (P c)}.
    #[global] Instance is_take_exceptionP_dec ev: Decision (is_take_exceptionP ev).
    Proof using Pdec. unfold is_take_exceptionP. solve_decision. Defined.
  End isTakeException.
  Notation is_take_exception := (is_take_exceptionP (λ _, True)).

  Definition is_return_exception ev := ev = ReturnException &→ ().
  #[global] Instance is_return_exception_dec ev :
    Decision (is_return_exception ev).
  Proof. destruct ev as [[]?]; (right + left); abstract (hauto q:on). Defined.

End Interface.

Module Type InterfaceT (A : Arch).
  Include Interface A.
End InterfaceT.

Module Type InterfaceWithArch.
  Declare Module Arch : Arch.
  Declare Module Interface : InterfaceT Arch.
End InterfaceWithArch.
