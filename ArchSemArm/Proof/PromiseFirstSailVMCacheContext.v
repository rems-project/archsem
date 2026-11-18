(******************************************************************************)
(* Context/promise exchange through observational cache replay                *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheRefill
  PromiseFirstSailVMCacheIndexed PromiseFirstSailVMCacheEvents
  PromiseFirstSailVMCacheIndex PromiseFirstSailVMCacheExchange
  PromiseFirstSailVMCacheConfig PromiseFirstSailVMCacheHistory PromiseFirstSailVMCacheRollback
  PromiseFirstSailVMCacheLastTLBI.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMCacheContext.
Import VMPromising VMCacheRefill VMCacheEvents VMCacheExchange VMCacheRollback.

Lemma rolled_valid time cache : VMCacheIndexed.valid cache → VMCacheIndexed.valid (rolled time cache).
Proof. intro Hvalid. eapply VMCacheIndexed.roll_back; [exact Hvalid|reflexivity]. Qed.

Lemma roots_valid f cache : VMCacheIndexed.valid cache →
  VMCacheIndexed.valid (set TLB.asid_roots f cache).
Proof. exact (λ H, H). Qed.

Local Opaque TLB.fill_from_roots TLB.fill_cse TLB.fill_asid_root TLB.fill_promise.

Lemma roots_equiv f old new : equiv old new →
  equiv (set TLB.asid_roots f old) (set TLB.asid_roots f new).
Proof. exact (λ H, H). Qed.

Theorem promise_rolled_equiv tid imem mem ev time old issued :
  time ≤ length mem →
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (issued, ()) →
  equiv (rolled time old) (rolled time issued).
Proof.
  intros Htime Hpromise.
  pose proof (VMCacheConfig.fill_promise tid imem (ev :: mem) ev old issued () Hpromise) as Hconfig.
  destruct (VMCacheIndex.fill_promise_frame_at tid imem mem ev time old issued Htime Hpromise)
    as [Hhistory _].
  split.
  - unfold VMCacheConfig.config in Hconfig. change (TLB.pte_present old = TLB.pte_present issued). congruence.
  - intro fe. unfold rolled. rewrite !history_map by reflexivity. apply Hhistory.
Qed.

Local Notation unique := VMCacheLastTLBI.unique.

Lemma rolled_unique time cache : unique cache → unique (rolled time cache).
Proof. apply VMCacheLastTLBI.unique_map_fe. Qed.

Theorem fill_cse_rolled_equiv tid imem mem time ttbr0 ttbr1 old new old' :
  VMCacheIndexed.valid old → VMCacheIndexed.valid new → unique old → unique new →
  equiv (rolled time old) (rolled time new) →
  TLB.fill_cse tid imem mem time ttbr0 ttbr1 old = Ok (old', ()) →
  ∃ new', TLB.fill_cse tid imem mem time ttbr0 ttbr1 new = Ok (new', ()) ∧ equiv old' new'.
Proof.
  intros Hvalid Hvalid' Hunique Hunique' Heq Hrun.
  set (roots := if ttbr1 is Some upper then
    [(bv_extract 48 16 ttbr0, ttbr0, false, time); (bv_extract 48 16 ttbr0, upper, true, time)]
    else [(bv_extract 48 16 ttbr0, ttbr0, false, time)]).
  change (TLB.fill_from_btw tid imem mem roots (S time) (length mem) mem
    (setv TLB.asid_roots roots (rolled time old)) = Ok (old', ())) in Hrun.
  change (∃ new', TLB.fill_from_btw tid imem mem roots (S time) (length mem) mem
    (setv TLB.asid_roots roots (rolled time new)) = Ok (new', ()) ∧ equiv old' new').
  eapply VMCacheLastTLBI.fill_from_btw_equiv with (old := setv TLB.asid_roots roots (rolled time old));
    [| | | |exact Heq|exact Hrun];
    first [apply roots_valid, rolled_valid; assumption|apply rolled_unique; assumption].
Qed.

Theorem fill_asid_root_rolled_equiv tid imem mem root time old new old' :
  VMCacheIndexed.valid old → VMCacheIndexed.valid new → unique old → unique new →
  TLB.asid_roots old = TLB.asid_roots new → equiv (rolled time old) (rolled time new) →
  TLB.fill_asid_root tid imem mem root time old = Ok (old', ()) →
  ∃ new', TLB.fill_asid_root tid imem mem root time new = Ok (new', ()) ∧ equiv old' new'.
Proof.
  intros Hvalid Hvalid' Hunique Hunique' Hroots Heq Hrun.
  set (before_old := set TLB.asid_roots (cons (root, time)) (rolled time old)).
  set (before_new := set TLB.asid_roots (cons (root, time)) (rolled time new)).
  change ((TLB.fill_from_roots imem mem time [root] before_old ≫=
    λ '(mid, _), TLB.fill_from_btw tid imem mem (TLB.asid_roots mid)
      (S time) (length mem) mem mid) = Ok (old', ())) in Hrun.
  change (∃ new', (TLB.fill_from_roots imem mem time [root] before_new ≫=
    λ '(mid, _), TLB.fill_from_btw tid imem mem (TLB.asid_roots mid)
      (S time) (length mem) mem mid) = Ok (new', ()) ∧ equiv old' new').
  destruct (TLB.fill_from_roots imem mem time [root] before_old) as [[mid []]|err] eqn:Hfirst;
    [|discriminate]. cbn [mbind result_bind] in Hrun.
  destruct (fill_from_roots_equiv imem mem time [root] before_old before_new mid () Heq Hfirst)
    as [mid' [Hfirst' Heq']].
  rewrite Hfirst'. cbn [mbind result_bind].
  pose proof (VMCacheRoots.fill_from_roots imem mem time [root] before_old mid () Hfirst) as Hroots_old.
  pose proof (VMCacheRoots.fill_from_roots imem mem time [root] before_new mid' () Hfirst') as Hroots_new.
  unfold VMCacheRoots.config in Hroots_old, Hroots_new.
  assert (Hmid_roots : TLB.asid_roots mid = TLB.asid_roots mid').
  { rewrite Hroots_old, Hroots_new. change ((root, time) :: TLB.asid_roots old = (root, time) :: TLB.asid_roots new). rewrite Hroots. reflexivity. }
  rewrite <- Hmid_roots.
  eapply VMCacheLastTLBI.fill_from_btw_equiv with (old := mid); [| | | |exact Heq'|exact Hrun].
  - eapply VMCacheIndexed.fill_from_roots; [|exact Hfirst].
    apply roots_valid, rolled_valid, Hvalid.
  - eapply VMCacheIndexed.fill_from_roots; [|exact Hfirst'].
    apply roots_valid, rolled_valid, Hvalid'.
  - eapply VMCacheLastTLBI.unique_fill_from_roots; [|exact Hfirst]. apply rolled_unique, Hunique.
  - eapply VMCacheLastTLBI.unique_fill_from_roots; [|exact Hfirst']. apply rolled_unique, Hunique'.
Qed.

(** The square permits allocations made only by the future promise, including
    when the replayed suffix contains local last-level invalidations. *)
Theorem fill_cse_exchange tid imem mem ev time ttbr0 ttbr1 old issued after_cse ending :
  time ≤ length mem → VMCacheIndexed.valid old → unique old →
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (issued, ()) →
  TLB.fill_cse tid imem mem time ttbr0 ttbr1 old = Ok (after_cse, ()) →
  TLB.fill_promise tid imem (ev :: mem) ev after_cse = Ok (ending, ()) →
  ∃ ending', TLB.fill_cse tid imem (ev :: mem) time ttbr0 ttbr1 issued = Ok (ending', ()) ∧
    equiv ending ending'.
Proof.
  intros Htime Hvalid Hunique Hpromise Hcse Hending.
  eapply fill_cse_rolled_equiv; [exact Hvalid| |exact Hunique| | |].
  - eapply VMCacheIndexed.fill_promise; eassumption.
  - eapply VMCacheLastTLBI.unique_fill_promise; eassumption.
  - eapply promise_rolled_equiv; eassumption.
  - rewrite (VMCacheHistory.fill_cse_future_promise tid imem mem ev time ttbr0 ttbr1 old after_cse Htime Hcse).
    exact Hending.
Qed.

Theorem fill_asid_root_exchange tid imem mem ev root time old issued after_root ending :
  time ≤ length mem → VMCacheIndexed.valid old → unique old →
  Forall (λ entry, entry.2 ≤ length mem) (TLB.asid_roots old) →
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (issued, ()) →
  TLB.fill_asid_root tid imem mem root time old = Ok (after_root, ()) →
  TLB.fill_promise tid imem (ev :: mem) ev after_root = Ok (ending, ()) →
  ∃ ending', TLB.fill_asid_root tid imem (ev :: mem) root time issued = Ok (ending', ()) ∧
    equiv ending ending'.
Proof.
  intros Htime Hvalid Hunique Hroots Hpromise Hroot Hending.
  eapply fill_asid_root_rolled_equiv; [exact Hvalid| |exact Hunique| | | |].
  - eapply VMCacheIndexed.fill_promise; eassumption.
  - eapply VMCacheLastTLBI.unique_fill_promise; eassumption.
  - symmetry. exact (VMCacheRoots.fill_promise tid imem (ev :: mem) ev old issued () Hpromise).
  - eapply promise_rolled_equiv; eassumption.
  - rewrite (VMCacheExchange.fill_asid_root_future_promise tid imem mem ev root time old after_root Htime Hroots Hroot).
    exact Hending.
Qed.


(** Besides entry histories, subsequent maintenance observes roots and ETS. *)
Definition observational (old new : TLB.t) :=
  equiv old new ∧ TLB.asid_roots old = TLB.asid_roots new ∧ TLB.ets old = TLB.ets new.

Lemma cse_square_observational tid imem mem ev time ttbr0 ttbr1 old issued ending after_cse ending' :
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (issued, ()) →
  TLB.fill_cse tid imem (ev :: mem) time ttbr0 ttbr1 issued = Ok (ending, ()) →
  TLB.fill_cse tid imem mem time ttbr0 ttbr1 old = Ok (after_cse, ()) →
  TLB.fill_promise tid imem (ev :: mem) ev after_cse = Ok (ending', ()) →
  equiv ending ending' → observational ending ending'.
Proof.
  intros Hp Hc Hc' Hp' Heq. split; [exact Heq|]. split.
  - pose proof (VMCacheHistory.fill_cse_roots tid imem (ev :: mem) time ttbr0 ttbr1 issued ending Hc) as H1.
    pose proof (VMCacheHistory.fill_cse_roots tid imem mem time ttbr0 ttbr1 old after_cse Hc') as H2.
    pose proof (VMCacheRoots.fill_promise tid imem (ev :: mem) ev after_cse ending' () Hp') as H3.
    unfold VMCacheRoots.config in H3. congruence.
  - pose proof (VMCacheConfig.fill_promise tid imem (ev :: mem) ev old issued () Hp) as H1.
    pose proof (VMCacheConfig.fill_cse tid imem (ev :: mem) time ttbr0 ttbr1 issued ending () Hc) as H2.
    pose proof (VMCacheConfig.fill_cse tid imem mem time ttbr0 ttbr1 old after_cse () Hc') as H3.
    pose proof (VMCacheConfig.fill_promise tid imem (ev :: mem) ev after_cse ending' () Hp') as H4.
    unfold VMCacheConfig.config in *. congruence.
Qed.

Lemma root_square_observational tid imem mem ev root time old issued ending after_root ending' :
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (issued, ()) →
  TLB.fill_asid_root tid imem (ev :: mem) root time issued = Ok (ending, ()) →
  TLB.fill_asid_root tid imem mem root time old = Ok (after_root, ()) →
  TLB.fill_promise tid imem (ev :: mem) ev after_root = Ok (ending', ()) →
  equiv ending ending' → observational ending ending'.
Proof.
  intros Hp Hc Hc' Hp' Heq. split; [exact Heq|]. split.
  - pose proof (VMCacheRoots.fill_promise tid imem (ev :: mem) ev old issued () Hp) as H1.
    pose proof (VMCacheExchange.fill_asid_root_roots tid imem (ev :: mem) root time issued ending Hc) as H2.
    pose proof (VMCacheExchange.fill_asid_root_roots tid imem mem root time old after_root Hc') as H3.
    pose proof (VMCacheRoots.fill_promise tid imem (ev :: mem) ev after_root ending' () Hp') as H4.
    unfold VMCacheRoots.config in *. congruence.
  - pose proof (VMCacheConfig.fill_promise tid imem (ev :: mem) ev old issued () Hp) as H1.
    pose proof (VMCacheConfig.fill_asid_root tid imem (ev :: mem) root time issued ending () Hc) as H2.
    pose proof (VMCacheConfig.fill_asid_root tid imem mem root time old after_root () Hc') as H3.
    pose proof (VMCacheConfig.fill_promise tid imem (ev :: mem) ev after_root ending' () Hp') as H4.
    unfold VMCacheConfig.config in *. congruence.
Qed.

(** Recover both steps of the exchanged execution from a successful
    promise-then-context execution; success of the other path is derived. *)
Theorem replay_cse_before_promise tid imem mem ev time ttbr0 ttbr1 old issued ending :
  time ≤ length mem → VMCacheIndexed.valid old → unique old →
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (issued, ()) →
  TLB.fill_cse tid imem (ev :: mem) time ttbr0 ttbr1 issued = Ok (ending, ()) →
  ∃ after_cse ending',
    TLB.fill_cse tid imem mem time ttbr0 ttbr1 old = Ok (after_cse, ()) ∧
    TLB.fill_promise tid imem (ev :: mem) ev after_cse = Ok (ending', ()) ∧
    observational ending ending'.
Proof.
  intros Htime Hvalid Hunique Hpromise Hcse.
  pose proof (VMCacheIndexed.fill_promise tid imem (ev :: mem) ev old issued () Hvalid Hpromise) as Hissued.
  pose proof (promise_rolled_equiv tid imem mem ev time old issued Htime Hpromise) as Hrolled.
  pose proof (VMCacheLastTLBI.unique_fill_promise tid imem (ev :: mem) ev old issued () Hunique Hpromise)
    as Hunique_issued.
  destruct (fill_cse_rolled_equiv tid imem (ev :: mem) time ttbr0 ttbr1 issued old ending
    Hissued Hvalid Hunique_issued Hunique (equiv_sym _ _ Hrolled) Hcse) as [ending' [Hrun Heq]].
  pose proof Hrun as Hsplit. rewrite VMCacheHistory.fill_cse_future in Hsplit by exact Htime.
  unfold mbind, st_bind, result_bind in Hsplit.
  destruct (TLB.fill_cse tid imem mem time ttbr0 ttbr1 old) as [[after_cse []]|err] eqn:Hbefore;
    [|discriminate].
  rewrite (VMCacheHistory.fill_cse_future_promise tid imem mem ev time ttbr0 ttbr1 old after_cse
    Htime Hbefore) in Hrun.
  exists after_cse, ending'. split; [reflexivity|]. split; [exact Hrun|].
  exact (cse_square_observational tid imem mem ev time ttbr0 ttbr1 old issued ending after_cse ending'
    Hpromise Hcse Hbefore Hrun Heq).
Qed.

Theorem replay_asid_root_before_promise tid imem mem ev root time old issued ending :
  time ≤ length mem → VMCacheIndexed.valid old → unique old →
  Forall (λ entry, entry.2 ≤ length mem) (TLB.asid_roots old) →
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (issued, ()) →
  TLB.fill_asid_root tid imem (ev :: mem) root time issued = Ok (ending, ()) →
  ∃ after_root ending',
    TLB.fill_asid_root tid imem mem root time old = Ok (after_root, ()) ∧
    TLB.fill_promise tid imem (ev :: mem) ev after_root = Ok (ending', ()) ∧
    observational ending ending'.
Proof.
  intros Htime Hvalid Hunique Hroots Hpromise Hroot.
  pose proof (VMCacheIndexed.fill_promise tid imem (ev :: mem) ev old issued () Hvalid Hpromise) as Hissued.
  pose proof (promise_rolled_equiv tid imem mem ev time old issued Htime Hpromise) as Hrolled.
  pose proof (VMCacheRoots.fill_promise tid imem (ev :: mem) ev old issued () Hpromise) as Hsame_roots.
  pose proof (VMCacheLastTLBI.unique_fill_promise tid imem (ev :: mem) ev old issued () Hunique Hpromise)
    as Hunique_issued.
  destruct (fill_asid_root_rolled_equiv tid imem (ev :: mem) root time issued old ending
    Hissued Hvalid Hunique_issued Hunique Hsame_roots (equiv_sym _ _ Hrolled) Hroot) as [ending' [Hrun Heq]].
  pose proof Hrun as Hsplit. rewrite VMCacheHistory.fill_asid_root_future in Hsplit by assumption.
  unfold mbind, st_bind, result_bind in Hsplit.
  destruct (TLB.fill_asid_root tid imem mem root time old) as [[after_root []]|err] eqn:Hbefore;
    [|discriminate].
  rewrite (VMCacheExchange.fill_asid_root_future_promise tid imem mem ev root time old after_root
    Htime Hroots Hbefore) in Hrun.
  exists after_root, ending'. split; [reflexivity|]. split; [exact Hrun|].
  exact (root_square_observational tid imem mem ev root time old issued ending after_root ending'
    Hpromise Hroot Hbefore Hrun Heq).
Qed.


Lemma observational_sym old new : observational old new → observational new old.
Proof.
  intros [Heq [Hroots Hets]]. split; [apply equiv_sym, Heq|]. split; symmetry; assumption.
Qed.

(** Moving the promise before a context change preserves histories, roots and ETS, once the earlier promise succeeds. *)
Theorem replay_promise_before_cse tid imem mem ev time ttbr0 ttbr1 old issued after_cse ending :
  time ≤ length mem → VMCacheIndexed.valid old → unique old →
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (issued, ()) →
  TLB.fill_cse tid imem mem time ttbr0 ttbr1 old = Ok (after_cse, ()) →
  TLB.fill_promise tid imem (ev :: mem) ev after_cse = Ok (ending, ()) →
  ∃ ending', TLB.fill_cse tid imem (ev :: mem) time ttbr0 ttbr1 issued = Ok (ending', ()) ∧
    observational ending ending'.
Proof.
  intros Htime Hvalid Hunique Hpromise Hcse Hending.
  destruct (fill_cse_exchange tid imem mem ev time ttbr0 ttbr1 old issued after_cse ending
    Htime Hvalid Hunique Hpromise Hcse Hending) as [ending' [Hrun Heq]].
  exists ending'. split; [exact Hrun|]. apply observational_sym.
  exact (cse_square_observational tid imem mem ev time ttbr0 ttbr1 old issued ending' after_cse ending
    Hpromise Hrun Hcse Hending (equiv_sym _ _ Heq)).
Qed.

Theorem replay_promise_before_asid_root tid imem mem ev root time old issued after_root ending :
  time ≤ length mem → VMCacheIndexed.valid old → unique old →
  Forall (λ entry, entry.2 ≤ length mem) (TLB.asid_roots old) →
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (issued, ()) →
  TLB.fill_asid_root tid imem mem root time old = Ok (after_root, ()) →
  TLB.fill_promise tid imem (ev :: mem) ev after_root = Ok (ending, ()) →
  ∃ ending', TLB.fill_asid_root tid imem (ev :: mem) root time issued = Ok (ending', ()) ∧
    observational ending ending'.
Proof.
  intros Htime Hvalid Hunique Hroots Hpromise Hroot Hending.
  destruct (fill_asid_root_exchange tid imem mem ev root time old issued after_root ending
    Htime Hvalid Hunique Hroots Hpromise Hroot Hending) as [ending' [Hrun Heq]].
  exists ending'. split; [exact Hrun|]. apply observational_sym.
  exact (root_square_observational tid imem mem ev root time old issued ending' after_root ending
    Hpromise Hrun Hroot Hending (equiv_sym _ _ Heq)).
Qed.

End VMCacheContext.
