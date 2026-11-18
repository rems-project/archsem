(******************************************************************************)
(* Outcome and instruction simulation after removing a foreign TLBI           *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheSim PromiseFirstSailVMSwapSim
  PromiseFirstSailVMSwapLookup PromiseFirstSailVMSwapInsert PromiseFirstSailVMSwapRemoveRun
  PromiseFirstSailVMSwapRemoveLocal PromiseFirstSailVMSwapRemoveRead PromiseFirstSailVMSwapRemoveCSE
  PromiseFirstSailVMSwapRemoveLoad PromiseFirstSailVMSwapRemoveRegWrite
  PromiseFirstSailVMSwapRemoveEffects PromiseFirstSailVMSwapRemoveStoreSim PromiseFirstSailVMSwapRemoveTLBISim
  PromiseFirstSailVMSwapRemoveInvariant PromiseFirstSailVMSwapRemoveCore
  PromiseFirstSailVMSwapPos PromiseFirstSailVMPageWrites PromiseFirstSailVMViews
  PromiseFirstSailVMSwapRemoveMap PromiseFirstSailVMSwapRemoveStamps.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveOutcome.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemoveRun VMSwapRemoveLocal VMCacheSimOutcome.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Lemma at_weaken {St A B} (R1 R2 : St → St → Prop) (V : A → B → Prop) m1 m2 a b :
  (∀ x y, R1 x y → R2 x y) → VMSwapInsert.esim_at R1 V m1 m2 a b →
  VMSwapInsert.esim_at R2 V m1 m2 a b.
Proof.
  intros Hweaken [Hr He]. split.
  - intros a' x Ha. destruct (Hr a' x Ha) as (b' & y & Hb & Hrel & Hv).
    exists b', y. split; [exact Hb|split; [apply Hweaken, Hrel|exact Hv]].
  - intros a' err Ha. destruct (He a' err Ha) as (b' & err' & Hb & Hrel).
    exists b', err'. split; [exact Hb|apply Hweaken, Hrel].
Qed.

Section Removed.
Context (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat).
Local Notation p := (S (length r)).
Local Notation g := (unshift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc epoch).
Local Notation R := (related r tlbi rc epoch).

Definition ok pp := VMSwapRemoveInvariant.ok p pp ∧ VMSwapPos.pp_pos pp ∧ VMPageWrites.ok pp ∧
  ∃ l, PPState.mem pp = l ++ e :: r ∧ VMSwapRemoveCore.core imem r tlbi rc epoch l (PPState.state pp).

Definition out_rel {A} (x y : A * option nat) := x.1 = y.1 ∧ y.2 = g <$> x.2.

Lemma run_outcome_ok n (tid : fin n) out pp pp' value : fin_to_nat tid ≠ rc → ok pp →
  Exec.elem_of_results (pp', value) (run_outcome n tid imem out pp) → ok pp'.
Proof.
  intros Hrc [Hinv [Hpos [Hpage [l [Hmem Hcore]]]]] Hrun. split.
  - eapply VMSwapRemoveInvariant.run_outcome_ok; eassumption.
  - split; [eapply VMSwapPos.run_outcome_pos; eassumption|].
    split; [eapply VMPageWrites.run_outcome_ok; eassumption|].
    eapply VMSwapRemoveCore.run_outcome_core; [exact Hrc|exact Hmem|apply Hinv|exact Hcore|exact Hrun].
Qed.

Lemma short_mem l a b : R a b → PPState.mem a = l ++ e :: r → PPState.mem b = l ++ r.
Proof.
  intros [[prefix [Ha Hb]] _] Hmem. rewrite Hmem in Ha. apply (app_inv_tail _ _ _) in Ha.
  subst prefix. exact Hb.
Qed.
Lemma mem_length a b : R a b → g (length (PPState.mem a)) = length (PPState.mem b).
Proof.
  intros [[l [-> ->]] _]. rewrite unshift_ge by (rewrite length_app; cbn; lia).
  rewrite !length_app. cbn. lia.
Qed.

Lemma read_imem_remove addr l :
  read_imem imem addr (l ++ e :: r) = read_imem imem addr (l ++ r).
Proof. unfold read_imem. rewrite (VMSwapInsert.read_initial_insert r tlbi rc epoch). reflexivity. Qed.

Ltac at_ret Hrel := apply VMSwapInsert.esim_at_of; [apply esim_ret; split; reflexivity|exact Hrel].
Ltac bind_eq := eapply (VMSwapInsert.esim_at_bind _ eq); [|
  let a' := fresh "a'" in let b' := fresh "b'" in let x := fresh "x" in let y := fresh "y" in
  let Ha := fresh "Ha" in let Hb := fresh "Hb" in let Hr := fresh "Hr" in
  intros a' b' x y Ha Hb Hr <-; at_ret Hr].
Ltac same_guard Hrel := eapply (VMSwapInsert.esim_at_bind _ eq);
  [apply VMSwapInsert.esim_at_of; [apply esim_guard_or_refl|exact Hrel]
  |let a' := fresh "a'" in let b' := fresh "b'" in let x := fresh "x" in let y := fresh "y" in
   let Ha := fresh "Ha" in let Hb := fresh "Hb" in let Hr := fresh "Hr" in
   intros a' b' x y Ha Hb Hr <-;
   apply Exec.elem_of_guard_or_inv in Ha as ->; apply Exec.elem_of_guard_or_inv in Hb as ->].

Lemma run_outcome_sim n (tid : fin n) out a b : fin_to_nat tid ≠ rc → R a b → ok a →
  VMSwapInsert.esim_at R out_rel (run_outcome n tid imem out) (run_outcome n tid imem out) a b.
Proof.
  intros Hrc Hrel [Hinv [Hpos [Hpage [l [Hmem [Hcore Hmsr]]]]]].
  destruct Hinv as [Hbound [Hthread [Hstamps Hiis]]].
  pose proof (VMSwapRemoveEffects.stamps_promises p _ Hstamps) as Hprom.
  assert (Heffect : VMSwapRemoveEffects.effect_rel r tlbi rc epoch a b) by (split; [exact Hrel|split; assumption]).
  pose proof (mem_length a b Hrel) as Hlen.
  destruct out.
  all: lazymatch goal with
    | |- context [run_outcome _ _ _ (MemRead ?mr)] => destruct mr as [? ? ? ? [|?]]
    | |- context [run_outcome _ _ _ (MemWrite ?mr _ _)] => destruct mr as [? ? ? ? [|?]]
    | _ => idtac end.
  all: simp run_outcome.
  all: try solve [apply VMSwapInsert.esim_at_of; [apply esim_throw|exact Hrel]].
  - (* RegRead *)
    bind_eq. apply VMSwapInsert.esim_at_of; [apply VMSwapRemoveRead.reg_read_sim|exact Hrel].
  - (* RegWrite *)
    bind_eq. eapply VMSwapRemoveRegWrite.run_reg_write_sim; eassumption.
  - (* MemRead *)
    same_guard Hrel. destruct (is_ifetch _); [|destruct (is_explicit _); [|destruct (is_ttw _)]].
    + same_guard Hrel. apply VMSwapInsert.esim_at_mget; [exact Hrel|].
      rewrite Hmem, (short_mem l a b Hrel Hmem), read_imem_remove.
      bind_eq. apply VMSwapInsert.esim_at_of; [|exact Hrel].
      apply esim_lift_res; [intros ? H; eexists; split; [exact H|reflexivity]|intros ? H; eexists; exact H].
    + bind_eq. apply VMSwapRemoveLoad.read_mem_sim; [exact Hrel|exact Hprom|intros t Ht; exact (VMSwapRemoveStamps.ok_inv _ _ Hiis t Ht)].
    + same_guard Hrel. bind_eq. apply VMSwapInsert.esim_at_of; [apply VMSwapRemoveRead.read_pte_sim|exact Hrel].
    + apply VMSwapInsert.esim_at_of; [apply esim_throw|exact Hrel].
  - (* MemWriteAddrAnnounce *)
    apply VMSwapInsert.esim_at_mget; [exact Hrel|].
    apply VMSwapInsert.esim_at_mget; [exact Hrel|].
    pose proof Hrel as [_ [Ht Hi]]. cbn [compose]. rewrite Hi.
    cbn [iis_map IIS.strict]. pose proof (proj1 Ht) as Hshape.
    assert (Hg : TState.no_write_promises_until (g (IIS.strict (PPState.iis a))) (PPState.state b) ↔
      TState.no_write_promises_until (IIS.strict (PPState.iis a)) (PPState.state a)).
    { rewrite Hshape. change (TState.no_write_promises_until (g (IIS.strict (PPState.iis a))) (ts_map g (PPState.state a)) ↔
        TState.no_write_promises_until (IIS.strict (PPState.iis a)) (PPState.state a)).
      apply (VMSwapRemoveMap.map_no_write_promises_until p ltac:(lia)), Hstamps. }
    apply VMSwapInsert.esim_at_of; [|exact Hrel].
    eapply esim_bind; [apply esim_guard_discard; apply Hg|intros ? ? _].
    eapply (esim_bind _ eq).
    { apply VMSwapRemoveCSE.update_state;
        [intro; symmetry; apply (VMSwapRemoveMap.map_vspec p ltac:(lia))|intros; reflexivity|intro; reflexivity]. }
    intros ? ? _. apply esim_ret. split; reflexivity.
  - (* MemWrite *)
    same_guard Hrel. same_guard Hrel.
    eapply (VMSwapInsert.esim_at_bind _ (λ x y : option nat, y = g <$> x)).
    + eapply (at_weaken (VMSwapRemoveEffects.effect_rel r tlbi rc epoch)); [intros ? ? H; apply H|].
      eapply VMSwapRemoveStoreSim.write_mem_sim; eassumption.
    + intros a' b' ret ret' Ha' Hb' Hrel' ->. at_ret Hrel'.
  - (* Barrier *)
    apply VMSwapInsert.esim_at_mget; [exact Hrel|]. bind_eq.
    eapply VMSwapRemoveCSE.run_barrier_sim;
      [exact Hrc|exact Hrel|exact Hmem|exact Hcore|exact Hprom|exact Hpage|lia|lia].
  - (* TlbOp *)
    apply VMSwapInsert.esim_at_mget; [exact Hrel|].
    pose proof Hrel as [_ [_ Hi]]. cbn [compose]. rewrite Hi. cbn [iis_map IIS.strict].
    eapply (VMSwapInsert.esim_at_bind _ (λ x y : option nat, y = g <$> x)).
    + eapply (at_weaken (VMSwapRemoveEffects.effect_rel r tlbi rc epoch)); [intros ? ? H; apply H|].
      eapply VMSwapRemoveTLBISim.run_tlbi_sim; eassumption.
    + intros a' b' ret ret' Ha' Hb' Hrel' ->. at_ret Hrel'.
  - (* TakeException *)
    apply VMSwapInsert.esim_at_mget; [exact Hrel|]. bind_eq.
    eapply VMSwapRemoveCSE.run_take_exception_sim;
      [exact Hrc|exact Hrel|exact Hmem|exact Hcore|exact Hbound|exact Hprom|exact Hpage|lia|lia].
  - (* ReturnException *)
    apply VMSwapInsert.esim_at_mget; [exact Hrel|]. bind_eq.
    eapply VMSwapRemoveCSE.run_cse_sim;
      [exact Hrc|exact Hrel|exact Hmem|exact Hcore|exact Hprom|exact Hpage|lia|lia].
  - (* TranslationStart *)
    bind_eq. eapply VMSwapRemoveLocal.run_trans_start_sim; eassumption.
  - (* TranslationEnd *)
    bind_eq. apply VMSwapInsert.esim_at_of; [apply VMSwapRemoveRead.trans_end_sim|exact Hrel].
Qed.

Theorem cinterp_sim n (tid : fin n) {A} (mon : iMon A) a b : fin_to_nat tid ≠ rc → R a b → ok a →
  VMSwapInsert.esim_at R eq (cinterp (run_outcome' n tid imem) mon) (cinterp (run_outcome' n tid imem) mon) a b.
Proof.
  intros Hrc. revert a b. induction mon as [value|call k IH]; intros a b Hrel Hok.
  - cbn. apply VMSwapInsert.esim_at_of; [apply esim_ret; reflexivity|exact Hrel].
  - destruct call as [out|[choices]]; cbn.
    + eapply (VMSwapInsert.esim_at_bind _ eq).
      * eapply (VMSwapInsert.esim_at_fmap _ out_rel); [apply run_outcome_sim; assumption|].
        intros x y [H _]. exact H.
      * intros a' b' x y Ha Hb Hr <-. apply IH; [exact Hr|].
        apply Exec.elem_of_fmap_inv in Ha as [res [_ Hout]]. eapply run_outcome_ok; eassumption.
    + eapply (VMSwapInsert.esim_at_bind _ eq).
      * apply VMSwapInsert.esim_at_of; [apply esim_mchoose|exact Hrel].
      * intros a' b' x y Ha Hb Hr <-. apply Exec.elem_of_mchoose_inv in Ha as ->.
        apply IH; assumption.
Qed.

Theorem instruction_ok n (tid : fin n) {A} (mon : iMon A) pp pp' value : fin_to_nat tid ≠ rc → ok pp →
  Exec.elem_of_results (pp', value) (cinterp (run_outcome' n tid imem) mon pp) → ok pp'.
Proof.
  intros Hrc. revert pp pp' value. induction mon as [ret|call k IH]; intros pp pp' value Hok Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exact Hok.
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[ret pre] [Heq Hout]]. cbn in Heq. subst res.
      eapply IH; [eapply run_outcome_ok; eassumption|exact Htail].
    + apply Exec.elem_of_bind_elim in Hrun as [mid [ret [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->. eapply IH; eassumption.
Qed.

(** A foreign recipient is the only thread restriction. The entry invariants
    are preserved along successful prefixes; error states carry [R]. *)
Theorem instruction_remove_sim n (tid : fin n) {A} (mon : iMon A) a b :
  fin_to_nat tid ≠ rc → R a b → ok a →
  (∀ a' value, Exec.elem_of_results (a', value) (cinterp (run_outcome' n tid imem) mon a) →
    ∃ b', Exec.elem_of_results (b', value) (cinterp (run_outcome' n tid imem) mon b) ∧ R a' b' ∧ ok a') ∧
  (∀ a' err, (a', err) ∈ Exec.errors (cinterp (run_outcome' n tid imem) mon a) →
    ∃ b' err', (b', err') ∈ Exec.errors (cinterp (run_outcome' n tid imem) mon b) ∧ R a' b').
Proof.
  intros Hrc Hrel Hok. destruct (cinterp_sim n tid mon a b Hrc Hrel Hok) as [Hr He].
  split; [|exact He]. intros a' value Hrun.
  destruct (Hr a' value Hrun) as (b' & value' & Hrun' & Hrel' & <-).
  exists b'. split; [exact Hrun'|]. split; [exact Hrel'|eapply instruction_ok; eassumption].
Qed.
End Removed.
End VMSwapRemoveOutcome.
