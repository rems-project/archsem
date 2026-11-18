(******************************************************************************)
(* Exact VM translation bounds after own and foreign promise emission        *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMGuards
  PromiseFirstSailVMLookup PromiseFirstSailVMTranslation.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMBoundsReplay.
Import VMPromising VMGuardReplay.
#[local] Typeclasses Transparent view UMPromising.view.

Lemma emit_promise_no_promises_until_inv tid imem mem ev ts issued v :
  TState.emit_promise tid imem (ev :: mem) ev ts = Ok issued →
  TState.no_promises_until v issued → TState.no_promises_until v ts.
Proof.
  intros Hpromise Hguard.
  pose proof (emit_promise_pending tid imem mem ev ts issued Hpromise) as [Hwr Htlbi].
  unfold TState.no_promises_until in *. rewrite Hwr, Htlbi in Hguard.
  intros p Hp. apply Hguard.
  destruct (bool_decide (Ev.tid ev = tid)); [destruct ev|].
  - right. exact Hp.
  - apply elem_of_app in Hp as [Hp|Hp]; apply elem_of_app.
    + left. exact Hp.
    + right. right. exact Hp.
  - exact Hp.
Qed.

(** Capping the new minimum at the former end of memory recovers exactly
    the former minimum, regardless of pending promises already in the state. *)
Lemma emit_promise_min_cap tid imem mem ev ts issued :
  TState.emit_promise tid imem (ev :: mem) ev ts = Ok issued →
  min (S (length mem)) (TState.min_promise (S (length mem)) issued) =
    TState.min_promise (length mem) ts.
Proof.
  intro Hpromise.
  pose proof (min_promise_bound (length mem) ts) as Hbound.
  pose proof (emit_promise_min_bound tid imem mem ev ts issued
    (length mem) (S (length mem)) Hpromise ltac:(lia) ltac:(lia)) as Hgrowth.
  apply Nat.le_antisymm; [|lia].
  destruct (min (S (length mem)) (TState.min_promise (S (length mem)) issued))
    as [|v] eqn:Hmin; [lia|].
  assert (Hlt : v < TState.min_promise (S (length mem)) issued) by lia.
  apply min_promise_gt in Hlt as [_ Hguard].
  assert (Hold : v < TState.min_promise (length mem) ts).
  { apply min_promise_gt. split; [lia|].
    eapply emit_promise_no_promises_until_inv; eassumption. }
  lia.
Qed.

Lemma emit_own_promise_min tid imem mem ev ts issued :
  Ev.tid ev = tid →
  TState.emit_promise tid imem (ev :: mem) ev ts = Ok issued →
  TState.min_promise (S (length mem)) issued = TState.min_promise (length mem) ts.
Proof.
  intros Howner Hpromise.
  pose proof (emit_promise_pending tid imem mem ev ts issued Hpromise) as [Hwr Htlbi].
  rewrite bool_decide_true in Hwr, Htlbi by exact Howner.
  assert (Hpending : S (length mem) ∈ (TState.prom_wr issued ++ TState.prom_tlbi issued)%list).
  { rewrite Hwr, Htlbi. destruct ev; apply elem_of_app.
    - left. left; reflexivity.
    - right. left; reflexivity. }
  assert (Hbound : TState.min_promise (S (length mem)) issued ≤ S (length mem)).
  { destruct (decide (TState.min_promise (S (length mem)) issued ≤ S (length mem)));
      [assumption|].
    assert (Hgt : S (length mem) < TState.min_promise (S (length mem)) issued) by lia.
    apply min_promise_gt in Hgt as [_ Hguard]. specialize (Hguard _ Hpending). lia. }
  pose proof (emit_promise_min_cap tid imem mem ev ts issued Hpromise) as Hcap.
  rewrite Nat.min_r in Hcap by exact Hbound. exact Hcap.
Qed.

Theorem emit_promise_translation_bound_cases tid imem mem ev ts issued :
  TState.emit_promise tid imem (ev :: mem) ev ts = Ok issued →
  let old := pred (TState.min_promise (length mem) ts) in
  let new := pred (TState.min_promise (length (ev :: mem)) issued) in
  new = old ∨ (old = length mem ∧ new = S (length mem)).
Proof.
  intro Hpromise. cbn [length].
  pose proof (emit_promise_min_cap tid imem mem ev ts issued Hpromise) as Hcap.
  pose proof (min_promise_bound (S (length mem)) issued) as Hbound.
  destruct (decide (TState.min_promise (S (length mem)) issued ≤ S (length mem))).
  - rewrite Nat.min_r in Hcap by assumption. left. congruence.
  - right. split; lia.
Qed.

(** Moving an own promise across an earlier translation does not enlarge
    its query bound. Full cached-table and root lookup replay therefore uses
    the existing bounded-history theorem at the handler's actual bounds. *)
Theorem emit_own_promise_lookup tid imem mem ev ts issued ifetch upper vpn
    asid ttbr0 tmin_ok tmin_unc result :
  Ev.tid ev = tid →
  TState.emit_promise tid imem (ev :: mem) ev ts = Ok issued →
  Exec.elem_of_results result
    (TState.tlb_lookup tid imem mem ts ifetch upper vpn asid ttbr0 tmin_ok tmin_unc
      (pred (TState.min_promise (length mem) ts))) →
  ∃ result',
    Exec.elem_of_results result'
      (TState.tlb_lookup tid imem (ev :: mem) issued ifetch upper vpn asid ttbr0
        tmin_ok tmin_unc (pred (TState.min_promise (length (ev :: mem)) issued))) ∧
    VMTranslationReplay.same_translation (length mem) result result'.
Proof.
  intros Howner Hpromise Hlookup.
  cbn [length]. rewrite (emit_own_promise_min tid imem mem ev ts issued Howner Hpromise).
  eapply VMLookupReplay.emit_promise_lookup_replay; [exact Hpromise| |exact Hlookup].
  pose proof (min_promise_bound (length mem) ts). lia.
Qed.
End VMBoundsReplay.
