(******************************************************************************)
(* Bounded VM lookup replay after a future global promise                    *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCache
  PromiseFirstSailVMCacheFill PromiseFirstSailVMTranslation PromiseFirstCurrent
  PromiseFirstConcreteCurrent PromiseFirstSailVMReplay.

Module VMLookupReplay.
Import VMPromising VMTranslationReplay.
Local Open Scope nat_scope.
Local Open Scope stdpp.

Lemma read_all_pte_future addr imem mem event tmin tmax :
  tmax ≤ length mem →
  Memory.read_all_pte addr imem (event :: mem) tmin tmax =
  Memory.read_all_pte addr imem mem tmin tmax.
Proof.
  intro Hmax. unfold Memory.read_all_pte, Memory.read_all_btw,
    PromMemory.read_all_btw.
  destruct (decide (tmin ≤ tmax)); [|reflexivity].
  rewrite PromMemory.cut_before_cons_old by exact Hmax. reflexivity.
Qed.

Lemma uncacheable_same_translation bound old new ptes tmin tmax lvl :
  Forall2 (same_translation bound) old new →
  Forall2 (same_translation bound)
    (TLB.get_results_from_events_uncacheable_aux old ptes tmin tmax lvl)
    (TLB.get_results_from_events_uncacheable_aux new ptes tmin tmax lvl).
Proof.
  intro Hsame. revert ptes tmax.
  induction Hsame as [|old new olds news Hhead Htail IH]; intros ptes tmax.
  - constructor.
  - destruct old as [ttbr path start stop inv], new as [ttbr' path' start' stop' inv'].
    destruct Hhead as [Httbr [Hpath [Hstart [Hstop Hinv]]]].
    cbn in Httbr, Hpath, Hstart, Hstop, Hinv.
    subst ttbr' path' start' stop'.
    cbn [TLB.get_results_from_events_uncacheable_aux].
    revert tmax. induction ptes as [|[pte time] ptes IHptes]; intro tmax; [constructor|].
    cbn [TLB.Result.tstart TLB.Result.tend].
    destruct (decide (Nat.min stop tmax < tmin)); [constructor|].
    destruct (decide (time ≤ start));
      destruct (decide (is_tlb_fillable lvl pte));
      try (constructor; [apply same_translation_make, Hinv|]);
      first [apply IH|apply IHptes].
Qed.

Lemma table_future_prefix tid imem mem event ifetch vpn fe events prefix tmin tmax old :
  Forall (λ event, length mem < event.2) prefix → tmax ≤ length mem →
  TLB.get_result_from_table_FE tid imem mem ifetch vpn fe events tmin tmax = Ok old →
  ∃ new,
    TLB.get_result_from_table_FE tid imem (event :: mem) ifetch vpn fe
      (prefix ++ events)%list tmin tmax = Ok new ∧
    Forall2 (same_translation (length mem)) old new.
Proof.
  intros Hprefix Hmax. unfold TLB.get_result_from_table_FE.
  destruct (decide (tmax < tmin));
    [injection 1 as <-; exists []; split; [reflexivity|constructor]|].
  destruct (child_lvl (TLB.FE.lvl fe)) as [lvl|];
    [|injection 1 as <-; exists []; split; [reflexivity|constructor]].
  pose proof (future_prefix_translation_replay tid ifetch (TLB.FE.ttbr fe)
    (TLB.FE.ptes fe) (length mem) prefix events tmin tmax None Hprefix Hmax) as Hpre.
  destruct Hpre as [|first first' rest rest' Hfirst Hrest].
  - injection 1 as <-. exists []. split; [reflexivity|constructor].
  - rewrite read_all_pte_future by exact Hmax.
    destruct (Memory.read_all_pte _ imem mem tmin tmax) as [ptes|err];
      cbn; [|discriminate].
    injection 1 as <-. eexists. split; [reflexivity|].
    apply (uncacheable_same_translation (length mem)
      (first :: rest) (first' :: rest') ptes tmin tmax lvl).
    constructor; assumption.
Qed.

Lemma entry_future_prefix tid imem mem event ifetch vpn fe events prefix tmin_ok tmin_unc tmax old :
  Forall (λ event, length mem < event.2) prefix → tmax ≤ length mem →
  TLB.get_result_from_FE tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax = Ok old →
  ∃ new,
    TLB.get_result_from_FE tid imem (event :: mem) ifetch vpn fe
      (prefix ++ events)%list tmin_ok tmin_unc tmax = Ok new ∧
    Forall2 (same_translation (length mem)) old new.
Proof.
  intros Hprefix Hmax. unfold TLB.get_result_from_FE.
  destruct (decide (TLB.FE.is_table fe)).
  - apply table_future_prefix; assumption.
  - unfold TLB.get_result_from_leaf_FE.
    destruct (decide (tmax < tmin_ok)).
    + injection 1 as <-. exists []. split; [reflexivity|constructor].
    + injection 1 as <-. eexists. split; [reflexivity|].
      apply future_prefix_translation_replay; assumption.
Qed.

Lemma get_fes_witness cache ctxts fe events :
  (fe, events) ∈ TLB.get_fes cache ctxts ↔
  ∃ ctxt, ctxt ∈ ctxts ∧ (fe, events) ∈ TLB.VATLB.get_fe (TLB.vatlb cache) ctxt.
Proof.
  unfold TLB.get_fes. split.
  - intro Hin. apply list_elem_of_In, List.in_concat in Hin as [entries [Hin Hentry]].
    apply List.in_map_iff in Hin as [ctxt [<- Hin]].
    exists ctxt. split; apply list_elem_of_In; assumption.
  - intros [ctxt [Hin Hentry]]. apply list_elem_of_In, List.in_concat.
    exists (TLB.VATLB.get_fe (TLB.vatlb cache) ctxt). split.
    + apply List.in_map, list_elem_of_In, Hin.
    + apply list_elem_of_In, Hentry.
Qed.

Lemma lookup_witness tid imem mem cache ifetch upper vpn tmin_ok tmin_unc tmax asid result :
  Exec.elem_of_results result
    (TLB.lookup tid imem mem cache ifetch upper vpn tmin_ok tmin_unc tmax asid) ↔
  ∃ fe events candidates,
    (fe, events) ∈ TLB.get_fes cache
      (TLB.get_global_Ctxts upper vpn ++ TLB.get_asid_Ctxts upper vpn asid)%list ∧
    TLB.get_result_from_FE tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax =
      Ok candidates ∧ result ∈ candidates.
Proof.
  unfold TLB.lookup. split.
  - intro Hin. apply Exec.elem_of_res_bind_elim in Hin as [[fe events] [Hentry Hin]].
    apply Exec.elem_of_res_bind_elim in Hin as [candidates [Hget Hin]].
    exists fe, events, candidates. split.
    + apply Exec.elem_of_res_mchoosel_inv in Hentry. exact Hentry.
    + split; [apply PromiseFirstCurrent.lift_result_res_success, Hget|].
      apply Exec.elem_of_res_mchoosel_inv in Hin. exact Hin.
  - intros [fe [events [candidates [Hentry [Hget Hin]]]]].
    eapply Exec.elem_of_res_bind_intro with (a := (fe, events));
      [apply Exec.elem_of_res_mchoosel, Hentry|].
    eapply Exec.elem_of_res_bind_intro with (a := candidates).
    + apply PromiseFirstCurrent.lift_result_res_success, Hget.
    + apply Exec.elem_of_res_mchoosel, Hin.
Qed.

(** Future entry events and an appended memory event preserve each successful
    lookup within the old history's time bound. Errors in other entries do
    not enter the success premise. A future foreign TLBI may add a deadline
    beyond that bound; the address, PTE path, and valid interval are preserved. *)
Theorem bounded_lookup_replay tid imem mem event old new ifetch upper vpn
    tmin_ok tmin_unc tmax asid result :
  VMCacheReplay.extends (length mem) (TLB.vatlb old) (TLB.vatlb new) →
  tmax ≤ length mem →
  Exec.elem_of_results result
    (TLB.lookup tid imem mem old ifetch upper vpn tmin_ok tmin_unc tmax asid) →
  ∃ result',
    Exec.elem_of_results result'
      (TLB.lookup tid imem (event :: mem) new ifetch upper vpn tmin_ok tmin_unc tmax asid) ∧
    same_translation (length mem) result result'.
Proof.
  intros Hextends Hmax Hin.
  apply lookup_witness in Hin as [fe [events [candidates [Hentry [Hget Hin]]]]].
  apply get_fes_witness in Hentry as [ctxt [Hctxt Hentry]].
  destruct (Hextends ctxt fe events Hentry) as [prefix [Hprefix Hnew]].
  destruct (entry_future_prefix tid imem mem event ifetch vpn fe events prefix
    tmin_ok tmin_unc tmax candidates Hprefix Hmax Hget) as [candidates' [Hget' Hsame]].
  assert (Hcandidate : ∃ result', result' ∈ candidates' ∧
    same_translation (length mem) result result').
  { clear Hget Hget'. induction Hsame as [|first first' rest rest' Hfirst Hrest IH].
    - inversion Hin.
    - apply elem_of_cons in Hin as [->|Hin].
      + exists first'. split; [left; reflexivity|exact Hfirst].
      + destruct (IH Hin) as [result' [Hmember Hresult]].
        exists result'. split; [right; exact Hmember|exact Hresult]. }
  destruct Hcandidate as [result' [Hmember Hresult]].
  exists result'. split; [|exact Hresult].
  apply lookup_witness. exists fe, (prefix ++ events)%list, candidates'.
  split; [|auto]. apply get_fes_witness. exists ctxt. auto.
Qed.

Corollary fill_promise_lookup_replay tid imem mem event old new ifetch upper vpn
    tmin_ok tmin_unc tmax asid result :
  TLB.fill_promise tid imem (event :: mem) event old = Ok (new, ()) →
  tmax ≤ length mem →
  Exec.elem_of_results result
    (TLB.lookup tid imem mem old ifetch upper vpn tmin_ok tmin_unc tmax asid) →
  ∃ result',
    Exec.elem_of_results result'
      (TLB.lookup tid imem (event :: mem) new ifetch upper vpn tmin_ok tmin_unc tmax asid) ∧
    same_translation (length mem) result result'.
Proof.
  intro Hfill. apply bounded_lookup_replay.
  exact (VMCacheFillReplay.fill_promise_extends tid imem mem event old new Hfill).
Qed.

Lemma same_translation_refl bound result : same_translation bound result result.
Proof. repeat split; try reflexivity. left. reflexivity. Qed.

Local Lemma merge_success {E A} (result : A) (left right : Exec.res E A) :
  Exec.elem_of_results result (Exec.merge left right) ↔
  Exec.elem_of_results result left ∨ Exec.elem_of_results result right.
Proof. unfold Exec.elem_of_results, Exec.merge. cbn. apply elem_of_app. Qed.

Lemma thread_lookup_replay tid imem mem event old new ts ts' ifetch upper vpn
    asid ttbr0 tmin_ok tmin_unc tmax result :
  TState.tlb ts = Some old → TState.tlb ts' = Some new →
  TState.read_sreg_indirect ts' TTBR1_EL1 = TState.read_sreg_indirect ts TTBR1_EL1 →
  VMCacheReplay.extends (length mem) (TLB.vatlb old) (TLB.vatlb new) →
  tmax ≤ length mem →
  Exec.elem_of_results result
    (TState.tlb_lookup tid imem mem ts ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax) →
  ∃ result',
    Exec.elem_of_results result'
      (TState.tlb_lookup tid imem (event :: mem) ts' ifetch upper vpn
        asid ttbr0 tmin_ok tmin_unc tmax) ∧
    same_translation (length mem) result result'.
Proof.
  intros Hcache Hcache' Hsreg Hextends Hmax.
  unfold TState.tlb_lookup. rewrite Hcache, Hcache'.
  intro Hin. apply merge_success in Hin as [Hcached|Hroot].
  - destruct (bounded_lookup_replay tid imem mem event old new ifetch upper vpn
      tmin_ok tmin_unc tmax asid result Hextends Hmax Hcached) as [result' [Hin Hsame]].
    exists result'. split; [apply merge_success; left; exact Hin|exact Hsame].
  - exists result. split; [|apply same_translation_refl].
    apply merge_success. right. rewrite Hsreg.
    destruct (decide (tmin_unc ≤ tmax)); [|exact Hroot].
    apply Exec.elem_of_res_bind_elim in Hroot as [ttbrs [Hregs Hroot]].
    apply Exec.elem_of_res_bind_elim in Hroot as [[ttbr vttbr] [Hchoice Hroot]].
    apply Exec.elem_of_res_bind_elim in Hroot as [ptes [Hread Hroot]].
    eapply Exec.elem_of_res_bind_intro; [exact Hregs|].
    eapply Exec.elem_of_res_bind_intro; [exact Hchoice|].
    eapply Exec.elem_of_res_bind_intro with (a := ptes); [|exact Hroot].
    rewrite read_all_pte_future by exact Hmax. exact Hread.
Qed.

Lemma emit_promise_preserves_sreg tid imem mem event ts ts' reg :
  TState.emit_promise tid imem mem event ts = Ok ts' →
  TState.read_sreg_indirect ts' reg = TState.read_sreg_indirect ts reg.
Proof.
  unfold TState.emit_promise, TState.process_event.
  intro Hpromise. apply VMReadReplay.run_tlb_frame in Hpromise.
  rewrite Hpromise. destruct (bool_decide (Ev.tid event = tid));
    [destruct event|]; reflexivity.
Qed.

Theorem emit_promise_lookup_replay tid imem mem event ts ts' ifetch upper vpn
    asid ttbr0 tmin_ok tmin_unc tmax result :
  TState.emit_promise tid imem (event :: mem) event ts = Ok ts' →
  tmax ≤ length mem →
  Exec.elem_of_results result
    (TState.tlb_lookup tid imem mem ts ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax) →
  ∃ result',
    Exec.elem_of_results result'
      (TState.tlb_lookup tid imem (event :: mem) ts' ifetch upper vpn
        asid ttbr0 tmin_ok tmin_unc tmax) ∧
    same_translation (length mem) result result'.
Proof.
  intros Hpromise Hmax Hin. destruct (TState.tlb ts) as [old|] eqn:Hcache.
  - destruct (VMCacheFillReplay.emit_promise_cache_extends tid imem mem event
      ts ts' old Hcache Hpromise) as [new [Hcache' Hextends]].
    refine (thread_lookup_replay tid imem mem event old new ts ts' ifetch upper vpn
      asid ttbr0 tmin_ok tmin_unc tmax result Hcache Hcache' _ Hextends Hmax Hin).
    eapply emit_promise_preserves_sreg; eassumption.
  - unfold TState.tlb_lookup in Hin. rewrite Hcache in Hin. inversion Hin.
Qed.

End VMLookupReplay.

#[local] Typeclasses Transparent VMPromising.VMPromising Promising.mEvent Promising.tState.
#[local] Typeclasses Transparent VMPromising.Memory.t.

Theorem VMSail_global_promise_lookup_replay bbm {n} (tid : fin n) st next event
    ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax result :
  PState.promise (VMPromising.VMPromising bbm) event st = Ok next →
  (tmax ≤ length (PState.events st))%nat →
  Exec.elem_of_results result
    (VMPromising.TState.tlb_lookup tid (PState.initmem st) (PState.events st)
      (PState.tstate tid st) ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax) →
  ∃ result',
    Exec.elem_of_results result'
      (VMPromising.TState.tlb_lookup tid (PState.initmem next) (PState.events next)
        (PState.tstate tid next) ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax) ∧
    VMTranslationReplay.same_translation (length (PState.events st)) result result'.
Proof.
  intros Hpromise Hmax Hin.
  destruct (VMPromising_promise_success event st next Hpromise) as [Himem [Hmem Hstates]].
  rewrite Himem, Hmem. eapply VMLookupReplay.emit_promise_lookup_replay;
    [exact (Hstates tid)|exact Hmax|exact Hin].
Qed.

(** Both caches come from actual initialization and promise filling. The old
    root points to a mapped block at 0x1000; the new root points to unmapped
    memory at 0x2000. The query at time zero keeps its result, while a query
    including time one retains both that result and the new path's error.
    The counterexample to the original lookup is preserved at commit 7df9902. *)
Module VMLookupReplayExample.
Import VMPromising.
Open Scope stdpp.
Open Scope bv.

Definition imem : memoryMap :=
  ∅ |> mem_insert 0 8 4099 |> mem_insert 4096 8 1.
Definition regs : registerMap :=
  ∅ |> reg_insert TCR_EL1 0 |> reg_insert TTBR0_EL1 0
    |> reg_insert ID_AA64MMFR1_EL1 0.
Definition event := Ev.Msg (Msg.make 1 0 8 8195).
Definition old : TLB.t :=
  match TLB.init 0 imem regs with
  | Ok cache => cache
  | Error _ => TLB.make TLB.VATLB.init ∅ ∅ [] 0
  end.
Definition new : TLB.t :=
  match TLB.fill_promise 0 imem [event] event old with
  | Ok (cache, _) => cache
  | Error _ => old
  end.
Definition lookup mem cache :=
  TLB.lookup 0 imem mem cache false false 0 0 0 0 0.
Definition candidate := TLB.Result.make 0 [4099; 1] 0 0 None.

Lemma initialization : TLB.init 0 imem regs = Ok old.
Proof. reflexivity. Qed.

Lemma promise_succeeds :
  TLB.fill_promise 0 imem [event] event old = Ok (new, ()).
Proof. reflexivity. Qed.

Lemma history_extends :
  VMCacheReplay.extends 0 (TLB.vatlb old) (TLB.vatlb new).
Proof.
  exact (VMCacheFillReplay.fill_promise_extends 0 imem [] event old new
    promise_succeeds).
Qed.

Lemma lookup_before : lookup [] old = Exec.make [candidate] [].
Proof.
  vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal].
Qed.

Lemma lookup_after :
  lookup [event] new = Exec.make [candidate] [].
Proof.
  vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal].
Qed.

(** A foreign promise can increase the upper bound to the new history length.
    The failing alternative is retained alongside the old translation. *)
Lemma lookup_after_full_history ifetch :
  TLB.lookup 0 imem [event] new ifetch false 0 0 0 1 0 =
    Exec.make [TLB.Result.make 0 [4099; 1] 0 1 None]
      ["Memory read of unmapped bytes at 0x2000"].
Proof.
  destruct ifetch; vm_compute;
    repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal].
Qed.

Theorem successful_lookup_preserved :
  TLB.init 0 imem regs = Ok old ∧
  TLB.fill_promise 0 imem [event] event old = Ok (new, ()) ∧
  VMCacheReplay.extends 0 (TLB.vatlb old) (TLB.vatlb new) ∧
  lookup [] old = Exec.make [candidate] [] ∧
  lookup [event] new = Exec.make [candidate] [].
Proof.
  repeat split; try apply initialization; try apply promise_succeeds;
    try apply history_extends; try apply lookup_before; try apply lookup_after.
Qed.
End VMLookupReplayExample.
