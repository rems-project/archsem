(******************************************************************************)
(* Promise-first proof target for the installed sail-tiny-arm semantics       *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstMemoryCurrent PromiseFirstExecutionCurrent
  PromiseFirstConcreteCurrent PromiseFirstSailExecution PromiseFirstSailRead
  PromiseFirstSailControl PromiseFirstSailInstruction PromiseFirstSailReplay.

#[local] Open Scope stdpp.

(** These prefixes use the actual Sail instruction and the model's outcome
    handler. They include intermediate outcomes of certification, even when
    a later outcome discards the path. Continuing at an instruction boundary
    resets IIS and respects the program's termination condition. *)
Section SailPrefixes.
Context (prom : Promising.Model) (nondet : bool) {n : nat}
  (term : terminationCondition n) (initMs : archState n) (tid : fin n).
Local Notation ppState :=
  (PPState.t prom.(Promising.tState) prom.(Promising.mEvent) prom.(Promising.iis)).

Inductive SailThreadPrefix : memoryMap → ppState → iMon () → Prop :=
| SailThreadPrefix_start use_pf st :
    PromiseFirstReachable prom (sail_tiny_arm_sem nondet) term initMs use_pf st →
    CPState.terminated_ts prom (term !!! tid) (PState.tstate tid st) = false →
    SailThreadPrefix (PState.initmem st)
      (PPState.Make (PState.tstate tid st) (PState.events st)
        prom.(Promising.iis_init)) (sail_tiny_arm_sem nondet)
| SailThreadPrefix_outcome imem ppst ppst' out k ret vpre :
    SailThreadPrefix imem ppst (Next (inl out) k) →
    Exec.elem_of_results (ppst', (ret, vpre))
      (prom.(Promising.handle_outcome) n tid imem out ppst) →
    SailThreadPrefix imem ppst' (k ret)
| SailThreadPrefix_choice imem ppst choices k (i : fin choices) :
    SailThreadPrefix imem ppst (Next (inr (ChooseFin choices)) k) →
    SailThreadPrefix imem ppst (k i)
| SailThreadPrefix_next imem ppst :
    SailThreadPrefix imem ppst (Ret ()) →
    CPState.terminated_ts prom (term !!! tid) (PPState.state ppst) = false →
    SailThreadPrefix imem
      (PPState.Make (PPState.state ppst) (PPState.mem ppst)
        prom.(Promising.iis_init)) (sail_tiny_arm_sem nondet).

(** Both execution paths use these prefixes: ordinary interpretation and
    interpretation that additionally collects candidate promises. *)
Lemma sail_instruction_result_prefix imem (mon : iMon ()) ppst ppst' :
  SailThreadPrefix imem ppst mon →
  Exec.elem_of_results (ppst', ())
    (cinterp (λ out, prom.(Promising.handle_outcome) n tid imem out |$> fst)
      mon ppst) →
  SailThreadPrefix imem ppst' (Ret ()).
Proof.
  revert ppst ppst'.
  induction mon as [u|call k IH]; intros ppst ppst' Hprefix Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> ->].
    exact Hprefix.
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [ret [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[res pre] [Heq Hout]].
      cbn in Heq. subst ret.
      eapply IH; [|exact Htail].
      eapply SailThreadPrefix_outcome; eassumption.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [ret [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->.
      eapply IH; [|exact Htail].
      eapply SailThreadPrefix_choice. exact Hprefix.
Qed.

Lemma sail_collect_instruction_result_prefix imem base (mon : iMon ())
    proms ppst proms' ppst' :
  SailThreadPrefix imem ppst mon →
  Exec.elem_of_results ((proms', ppst'), ())
    (cinterp (CPState.run_outcome_with_promise prom tid imem base)
      mon (proms, ppst)) →
  SailThreadPrefix imem ppst' (Ret ()).
Proof.
  revert proms ppst proms' ppst'.
  induction mon as [u|call k IH]; intros proms ppst proms' ppst' Hprefix Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [Heq ->].
    inversion Heq; subst. exact Hprefix.
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun
        as [[proms_mid pp_mid] [ret [Hout Htail]]].
      destruct (collect_outcome_inv prom tid imem base out
        proms ppst proms_mid pp_mid ret Hout) as [pre [Hhandle _]].
      eapply IH; [|exact Htail].
      eapply SailThreadPrefix_outcome; eassumption.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [ret [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->.
      eapply IH; [|exact Htail].
      eapply SailThreadPrefix_choice. exact Hprefix.
Qed.
End SailPrefixes.

(** Coverage is about physical fetch requests produced by the actual
    semantics. In VM this follows address translation, so virtual PC ranges
    alone do not discharge it. The immutability field includes intermediate
    histories as well as histories returned by the runner. *)
Record SailNoSelfModifying (prom : Promising.Model) (nondet : bool)
    {n : nat} (term : terminationCondition n) (initMs : archState n)
    (read_byte : address → prom.(Promising.mEvent) → option (bv 8))
    (code : code_region) : Prop := {
  sail_observed_code_immutable :
    PromiseFirstNoSelfModifying prom (sail_tiny_arm_sem nondet)
      term initMs read_byte code;
  sail_prefix_code_immutable :
    ∀ tid imem ppst mon,
      SailThreadPrefix prom nondet term initMs tid imem ppst mon →
      no_self_modifying_history read_byte code (PPState.mem ppst);
  sail_fetch_code_covered :
    ∀ tid imem ppst req k,
      SailThreadPrefix prom nondet term initMs tid imem ppst
        (Next (inl (MemRead req)) k) →
      is_ifetch req.(MemReq.access_kind) = true →
      code_covers_range code req.(MemReq.address) req.(MemReq.size)
}.

Definition UMSailNoSelfModifying nondet {n}
    (term : terminationCondition n) initMs code : Prop :=
  SailNoSelfModifying UMPromising nondet term initMs Msg.read_byte code.

Definition VMSailNoSelfModifying bbm nondet {n}
    (term : terminationCondition n) initMs code : Prop :=
  SailNoSelfModifying (VMPromising.VMPromising bbm) nondet
    term initMs VMPromisingReadByte code.

(** The statements below record the broad equivalence target. They are not
    established by the current proof stack. PromiseFirstSailVMTLBIOrder proves
    that unrestricted VM direct-to-promise-first inclusion is false for the
    current recipient-order filter: two broadcast TLBIs separated by DSB ISH
    have a direct final result and no promise-first final result at any fuel.
    Translation is enabled, BBM is disabled, the program performs no stores,
    and the relevant searches are complete. The filter must be repaired before
    a whole-program VM inclusion theorem can hold.
    PromiseFirstSailSerialization proves replay of the final batch;
    PromiseFirstSailScheduling identifies unstable OutOfFuel certificates
    in the promise-first-to-direct direction.
    PromiseFirstSailNoFuel closes that case for UM and VM when certification
    searches at the budgets of a successful promise-first run are complete:
    the direct runner produces the same architectural final result at every
    sufficiently large fuel. Completeness is required along that run, rather
    than at all natural-number budgets.
    UMSail_instruction_promise_replay below proves replay of one complete
    actual UM Sail instruction after prepromising its unique new message.
    PromiseFirstSailThreadNormalization moves all new messages of a terminating
    UM thread execution into a prefix of fuel-stable promise steps, including
    fulfillment of older promises and IIS resets. ThreadCertification also
    stabilizes OutOfFuel candidates with a terminating continuation.
    PromiseFirstSailInterleaving moves all messages of an interleaved UM
    instruction trace into a promise prefix using separately extracted fuel
    for each step, preserving the complete final state. Scheduling combines a
    stable promise prefix and final batch under one decreasing runner budget.
    PromiseFirstSailMixed transports a completed UM certificate before a
    fixed-history instruction prefix, including error-ending certificates.
    PromiseFirstSailOwnership derives the candidate's thread ownership from
    certification. Mixed then normalizes any interleaving of stable promises
    and fixed-history instructions, preserving the complete endpoint.
    PromiseFirstSailFinalization converts a fixed-history instruction suffix
    into a final batch when final minimum-promise views are bounded by memory.
    PromiseFirstSailDirect connects this to the actual promise-first runner:
    complete direct fulfillment witnesses preserve their architectural result
    at every sufficiently large fuel. Its single-thread result also permits
    fresh writes, using the terminating continuation to stabilize certificates.
    Both results keep the final view bound explicit. PromiseFirstSailUMStore
    inhabits the complete fulfillment witness with an actual Sail store and
    proves a shared direct/promise-first final result.
    PromiseFirstSailUMMixedDirect normalizes arbitrary interleavings of fresh
    writes and explicit promises for any finite number of threads. Actual
    direct results transfer to the promise-first runner under the final view
    bound and completeness of candidate-bearing searches exposed by this
    normalization. Completeness only at the original direct searches or at one
    larger fuel is not assumed to establish this premise. Without it, the
    theorem gives a promise-first result or a reachable unstable candidate
    whose enumeration reports OutOfFuel. PromiseFirstSailUMTwoThread proves
    the selected searches complete for two actual Sail stores and preserves
    the result of a direct path mixing a fresh write and an explicit promise.
    The original VM lookup counterexample is preserved at commit 7df9902.
    With the lookup fix, PromiseFirstSailVMLookup proves that an actual global
    promise preserves successful lookup candidates within the old history's
    time bound, including table walks and invalid L0 candidates. Future foreign
    TLBIs can add deadlines beyond that bound. PromiseFirstSailVMRootWrite
    provides a complete promise-first run and a shared direct final result for
    the actual Sail root-PTE write. PromiseFirstSailVMDirect certifies bounded
    fixed-history VM instruction suffixes with the actual handlers and final
    BBM validation. PromiseFirstSailVMRootDirect proves direct-to-promise-first
    inclusion for every successful direct run of the root-PTE program at any
    fuel, with translation enabled and BBM checking disabled. Full VM replay
    with interleaved new events, growing query bounds, and context changes
    remains open. *)
Definition UMSailPromiseFirstClaim : Prop :=
  ∀ nondet n (term : terminationCondition n) initMs code,
    UMSailNoSelfModifying nondet term initMs code →
    UMPromisingFinalStateEquiv (sail_tiny_arm_sem nondet) term initMs.

Definition VMSailPromiseFirstClaim : Prop :=
  ∀ bbm nondet n (term : terminationCondition n) initMs code,
    VMSailNoSelfModifying bbm nondet term initMs code →
    VMPromisingFinalStateEquiv bbm (sail_tiny_arm_sem nondet) term initMs.

Lemma sail_fetch_excludes_empty_code prom nondet {n}
    (term : terminationCondition n) initMs read_byte tid imem ppst req k :
  SailNoSelfModifying prom nondet term initMs read_byte (λ _, False) →
  SailThreadPrefix prom nondet term initMs tid imem ppst
    (Next (inl (MemRead req)) k) →
  is_ifetch req.(MemReq.access_kind) = true →
  (0 < req.(MemReq.size))%N → False.
Proof.
  intros Hsafe Hprefix Hfetch Hsize.
  pose proof (sail_fetch_code_covered _ _ _ _ _ _ Hsafe
    tid imem ppst req k Hprefix Hfetch) as Hcode.
  apply (Hcode req.(MemReq.address)).
  apply addr_in_range_spec. exists 0%N.
  split; [apply addr_addN_zero|exact Hsize].
Qed.

Lemma UMSail_candidate_preserves_fetch nondet {n}
    (term : terminationCondition n) initMs code use_pf st tid fuel msg
    fetch_tid imem ppst req k :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet)
    term initMs use_pf st →
  msg ∈ (CPState.enumerate_results (sail_tiny_arm_sem nondet) UMPromising
    term tid (PState.initmem st) fuel (PState.tstate tid st) (PState.events st))
    .(CPState.promises UMPromising) →
  SailThreadPrefix UMPromising nondet term initMs fetch_tid imem ppst
    (Next (inl (MemRead req)) k) →
  is_ifetch req.(MemReq.access_kind) = true → req.(MemReq.size) = 4%N →
  UMPromising.read_ifetch req.(MemReq.address) imem (msg :: PPState.mem ppst) =
  UMPromising.read_ifetch req.(MemReq.address) imem (PPState.mem ppst).
Proof.
  intros Hsafe Hreach Hcandidate Hprefix Hfetch Hsize.
  pose proof (sail_fetch_code_covered _ _ _ _ _ _ Hsafe
    fetch_tid imem ppst req k Hprefix Hfetch) as Hcode.
  rewrite Hsize in Hcode.
  pose proof (UMPromising_enumerated_promise_misses_code
    (sail_tiny_arm_sem nondet) term initMs code use_pf st tid fuel msg
    (sail_observed_code_immutable _ _ _ _ _ _ Hsafe) Hreach Hcandidate) as Hmiss.
  unfold UMPromising.read_ifetch, UMPromising.Memory.read_initial.
  rewrite (read_initial_cons_code_miss Some code req.(MemReq.address) 4
    imem (PPState.mem ppst) msg).
  - reflexivity.
  - lia.
  - exact Hcode.
  - intros msg' Heq. inversion Heq; subst. exact Hmiss.
Qed.

Lemma VMSail_candidate_preserves_fetch bbm nondet {n}
    (term : terminationCondition n) initMs code use_pf st tid fuel ev
    fetch_tid imem ppst req k :
  VMSailNoSelfModifying bbm nondet term initMs code →
  PromiseFirstReachable (VMPromising.VMPromising bbm) (sail_tiny_arm_sem nondet)
    term initMs use_pf st →
  ev ∈ (CPState.enumerate_results (sail_tiny_arm_sem nondet)
    (VMPromising.VMPromising bbm) term tid (PState.initmem st) fuel
    (PState.tstate tid st) (PState.events st))
    .(CPState.promises (VMPromising.VMPromising bbm)) →
  SailThreadPrefix (VMPromising.VMPromising bbm) nondet term initMs
    fetch_tid imem ppst (Next (inl (MemRead req)) k) →
  is_ifetch req.(MemReq.access_kind) = true → req.(MemReq.size) = 4%N →
  VMPromising.read_imem imem req.(MemReq.address) (ev :: PPState.mem ppst) =
  VMPromising.read_imem imem req.(MemReq.address) (PPState.mem ppst).
Proof.
  intros Hsafe Hreach Hcandidate Hprefix Hfetch Hsize.
  pose proof (sail_fetch_code_covered _ _ _ _ _ _ Hsafe
    fetch_tid imem ppst req k Hprefix Hfetch) as Hcode.
  rewrite Hsize in Hcode.
  pose proof (VMPromising_enumerated_promise_misses_code bbm
    (sail_tiny_arm_sem nondet) term initMs code use_pf st tid fuel ev
    (sail_observed_code_immutable _ _ _ _ _ _ Hsafe) Hreach Hcandidate) as Hmiss.
  unfold VMPromising.read_imem, VMPromising.Memory.read_initial.
  rewrite (read_initial_cons_code_miss Ev.get_msg code req.(MemReq.address) 4
    imem (PPState.mem ppst) ev).
  - reflexivity.
  - lia.
  - exact Hcode.
  - intros msg Hmsg a Ha.
    specialize (Hmiss a Ha). unfold VMPromisingReadByte in Hmiss.
    rewrite Hmsg in Hmiss. exact Hmiss.
Qed.

(** Replaying an actual Sail memory-read outcome after adding an enumerated
    promise from the same thread. No-self-modification discharges the fetch
    case; explicit reads retain their existing byte/timestamp choice. *)
#[local] Typeclasses Transparent UMPromising Promising.mEvent Promising.tState Promising.iis.
Lemma UMSail_mem_read_after_candidate nondet {n}
    (term : terminationCondition n) initMs code use_pf st tid fuel msg
    imem ppst req k ppst' ret pre :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet)
    term initMs use_pf st →
  msg ∈ (CPState.enumerate_results (sail_tiny_arm_sem nondet) UMPromising
    term tid (PState.initmem st) fuel (PState.tstate tid st) (PState.events st))
    .(CPState.promises UMPromising) →
  SailThreadPrefix UMPromising nondet term initMs tid imem ppst
    (Next (inl (MemRead req)) k) →
  Exec.elem_of_results (ppst', (ret, pre))
    (UMPromising.run_outcome tid imem (MemRead req) ppst) →
  let p := S (length (PPState.mem ppst)) in
  Exec.elem_of_results
    (UMReadReplay.add_pending_message msg p ppst', (ret, pre))
    (UMPromising.run_outcome tid imem (MemRead req)
      (UMReadReplay.add_pending_message msg p ppst)).
Proof.
  intros Hsafe Hreach Hcandidate Hprefix Hrun.
  apply UMOutcomeReplay.mem_read_after_promise; [|exact Hrun].
  intros Hfetch Hsize.
  eapply UMSail_candidate_preserves_fetch; eassumption.
Qed.

Lemma UMSail_prefix_preserved_fetches nondet {n}
    (term : terminationCondition n) initMs code (tid : fin n) imem msg mon ppst :
  UMSailNoSelfModifying nondet term initMs code →
  event_misses_code Msg.read_byte code msg →
  SailThreadPrefix UMPromising nondet term initMs tid imem ppst mon →
  UMInstructionReplay.preserved_fetches tid imem msg mon ppst.
Proof.
  intros Hsafe Hmiss. revert ppst.
  induction mon as [u|call k IH]; intros ppst Hprefix; [exact I|].
  destruct call as [out|[choices]]; cbn [UMInstructionReplay.preserved_fetches].
  - split.
    + destruct out; cbn [UMControlReplay.fetch_preserved]; try exact I.
      intros Hfetch Hsize.
      pose proof (sail_fetch_code_covered _ _ _ _ _ _ Hsafe
        tid imem ppst mr k Hprefix Hfetch) as Hcode.
      rewrite Hsize in Hcode.
      unfold UMPromising.read_ifetch, UMPromising.Memory.read_initial.
      rewrite (read_initial_cons_code_miss Some code (MemReq.address mr) 4
        imem (PPState.mem ppst) msg).
      * reflexivity.
      * lia.
      * exact Hcode.
      * intros msg' Heq. injection Heq as <-. exact Hmiss.
    + intros after ret pre Hout. apply IH.
      eapply SailThreadPrefix_outcome; eassumption.
  - intro r. apply IH. eapply SailThreadPrefix_choice. exact Hprefix.
Qed.

(** The complete actual Sail instruction can replay its newly created write
    from a state where that message was promised before the instruction. *)
Lemma UMSail_instruction_promise_replay nondet {n}
    (term : terminationCondition n) initMs code (tid : fin n) imem ppst ppst' :
  UMSailNoSelfModifying nondet term initMs code →
  SailThreadPrefix UMPromising nondet term initMs tid imem ppst
    (sail_tiny_arm_sem nondet) →
  Exec.elem_of_results (ppst', ())
    (cinterp (UMPromising.run_outcome' tid imem) (sail_tiny_arm_sem nondet) ppst) →
  PPState.mem ppst' ≠ PPState.mem ppst →
  ∃ msg,
    Msg.tid msg = (tid : nat) ∧
    PPState.mem ppst' = msg :: PPState.mem ppst ∧
    Exec.elem_of_results (ppst', ())
      (cinterp (UMPromising.run_outcome' tid imem) (sail_tiny_arm_sem nondet)
        (UMReadReplay.add_pending_message msg (S (length (PPState.mem ppst))) ppst)).
Proof.
  intros Hsafe Hprefix Hrun Hchanged.
  destruct (UMSail_instruction_updating_outcome_replay nondet tid imem ppst ppst' Hrun Hchanged)
    as [msg [out [before [after [r [pre [Howner [Hmem _]]]]]]]].
  assert (Hfinal : SailThreadPrefix UMPromising nondet term initMs tid imem ppst' (Ret ())).
  { eapply sail_instruction_result_prefix; eassumption. }
  pose proof (sail_prefix_code_immutable _ _ _ _ _ _ Hsafe
    tid imem ppst' (Ret ()) Hfinal) as Hcode.
  rewrite Hmem in Hcode.
  assert (Hmiss : event_misses_code Msg.read_byte code msg).
  { apply Hcode. left; reflexivity. }
  pose proof (UMSail_prefix_preserved_fetches nondet term initMs code tid imem msg
    (sail_tiny_arm_sem nondet) ppst Hsafe Hmiss Hprefix) as Hfetch.
  destruct (UMInstructionReplay.one_update_replay tid imem msg (sail_tiny_arm_sem nondet)
    ppst ppst' () (sail_tiny_arm_at_most_one_update nondet) Hfetch Hrun Hmem)
    as [_ Hreplay].
  exists msg. repeat split; assumption.
Qed.
