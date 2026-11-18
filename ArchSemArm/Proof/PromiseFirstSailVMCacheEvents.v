(******************************************************************************)
(* Replay of writes and non-last invalidations across dormant allocations     *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheRefill
  PromiseFirstSailVMCacheTraversal PromiseFirstSailVMCacheIndexed
  PromiseFirstSailVMCacheIndex PromiseFirstSailVMCacheHistory.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMCacheEvents.
Import VMPromising VMCacheRefill VMCacheTraversal.
#[local] Existing Instance TLB.Decision_affects.

Lemma history_map f cache fe : f fe [] = [] →
  history (set TLB.vatlb (TLB.VATLB.map_fe f) cache) fe = f fe (history cache fe).
Proof.
  intro Hempty. unfold history. cbn [TLB.vatlb]. rewrite VMCacheIndex.lookup_map_fe.
  destruct (TLB.vatlb cache !! fe) as [events|]; [reflexivity|symmetry; exact Hempty].
Qed.
Lemma map_equiv f old new :
  (∀ fe, f fe [] = []) → equiv old new →
  equiv (set TLB.vatlb (TLB.VATLB.map_fe f) old) (set TLB.vatlb (TLB.VATLB.map_fe f) new).
Proof.
  intros Hempty [Hconfig Hhist]. split; [exact Hconfig|]. intro fe.
  rewrite !history_map by apply Hempty. rewrite Hhist. reflexivity.
Qed.

Local Opaque TLB.fill_root TLB.fill_from_entries TLB.fill_from_roots TLB.get_relevant_entries.

Theorem fill_write_equiv imem mem time roots msg old new old' :
  VMCacheIndexed.valid old → VMCacheIndexed.valid new → equiv old new →
  TLB.fill_write imem mem time roots msg old = Ok (old', ()) →
  ∃ new', TLB.fill_write imem mem time roots msg new = Ok (new', ()) ∧ equiv old' new'.
Proof.
  intros Hvalid Hvalid' Heq Hrun.
  unfold TLB.fill_write, guard_or in Hrun |- *.
  destruct (decide (pa_to_pn (Msg.addr msg) =
    pa_to_pn (addr_addN (Msg.addr msg) (N.pred (Msg.size msg))))); [|discriminate].
  unfold mbind, st_bind, result_bind in Hrun |- *. cbn in Hrun |- *.
  set (selected := filter (λ '(_, ttbr, _), ttbr_root_table ttbr = pa_to_pn (Msg.addr msg)) roots) in *.
  destruct (TLB.fill_root imem mem time selected old) as [[mid loaded]|err] eqn:Hroots; [|discriminate].
  cbn in Hrun. rewrite VMCacheIndexed.relevant_run in Hrun. cbn in Hrun.
  destruct (fill_root_equiv imem mem time selected old new mid loaded Heq Hroots)
    as [mid' [Hroots' Heq']].
  pose proof (VMCacheIndexed.fill_root imem mem time selected old mid loaded Hvalid Hroots) as Hmid.
  pose proof (VMCacheIndexed.fill_root imem mem time selected new mid' loaded Hvalid' Hroots') as Hmid'.
  rewrite Hroots'. cbn. rewrite VMCacheIndexed.relevant_run. cbn.
  eapply fill_from_entries_permutation; [exact Heq'| |exact Hrun].
  apply Permutation_app_head. apply VMCacheIndexed.relevant_permutation; assumption.
Qed.

Theorem fill_tlbi_nonlast_equiv imem mem time roots tlbi old new old' :
  TLBI.last tlbi = false → equiv old new →
  TLB.fill_tlbi imem mem time roots tlbi old = Ok (old', ()) →
  ∃ new', TLB.fill_tlbi imem mem time roots tlbi new = Ok (new', ()) ∧ equiv old' new'.
Proof.
  intros Hlast Heq Hrun. unfold TLB.fill_tlbi in Hrun |- *. rewrite Hlast in Hrun |- *.
  set (invalidate := λ fe events, if decide (TLB.affects tlbi fe) then
    (if events is [] then [] else (TLB.Entry.Tlbi (TLBI.tid tlbi), time) :: events) else events) in *.
  change (TLB.fill_from_roots imem mem time roots
    (set TLB.vatlb (TLB.VATLB.map_fe invalidate) old) = Ok (old', ())) in Hrun.
  change (∃ new', TLB.fill_from_roots imem mem time roots
    (set TLB.vatlb (TLB.VATLB.map_fe invalidate) new) = Ok (new', ()) ∧ equiv old' new').
  eapply fill_from_roots_equiv; [|exact Hrun]. apply map_equiv; [|exact Heq].
  intro fe. unfold invalidate. destruct (decide (TLB.affects tlbi fe)); reflexivity.
Qed.

Definition regular tid ev :=
  match ev with
  | Ev.Msg _ => True
  | Ev.Tlbi tlbi recipient _ => tid ≠ recipient ∨ TLBI.last tlbi = false
  end.

Local Opaque TLB.fill_write TLB.fill_tlbi.

Theorem fill_event_equiv tid imem mem time roots ev old new old' :
  regular tid ev → VMCacheIndexed.valid old → VMCacheIndexed.valid new → equiv old new →
  TLB.fill_event tid imem mem time roots ev old = Ok (old', ()) →
  ∃ new', TLB.fill_event tid imem mem time roots ev new = Ok (new', ()) ∧ equiv old' new'.
Proof.
  intros Hregular Hvalid Hvalid' Heq Hrun.
  destruct ev as [msg|tlbi recipient epoch]; cbn [regular] in Hregular; cbn [TLB.fill_event] in Hrun |- *.
  - exact (fill_write_equiv imem mem time roots msg old new old' Hvalid Hvalid' Heq Hrun).
  - destruct (decide (tid = recipient)) as [Hrecipient|Hrecipient].
    + eapply fill_tlbi_nonlast_equiv with (old := old); [destruct Hregular; [contradiction|assumption]|exact Heq|exact Hrun].
    + change (@Ok string _ (old, ()) = Ok (old', ())) in Hrun. injection Hrun as <-.
      exists new. split; [reflexivity|exact Heq].
Qed.

Theorem fill_from_btw_equiv tid imem fullmem roots tmin tmax mem old new old' :
  Forall (regular tid) mem → VMCacheIndexed.valid old → VMCacheIndexed.valid new → equiv old new →
  TLB.fill_from_btw tid imem fullmem roots tmin tmax mem old = Ok (old', ()) →
  ∃ new', TLB.fill_from_btw tid imem fullmem roots tmin tmax mem new = Ok (new', ()) ∧ equiv old' new'.
Proof.
  revert roots mem old new old'. induction tmax as [|tmax IH];
    intros roots mem old new old' Hregular Hvalid Hvalid' Heq Hrun;
    cbn [TLB.fill_from_btw] in Hrun |- *; destruct (decide (_ < _)).
  - change (@Ok string _ (old, ()) = Ok (old', ())) in Hrun. injection Hrun as <-.
    exists new. auto.
  - discriminate.
  - change (@Ok string _ (old, ()) = Ok (old', ())) in Hrun. injection Hrun as <-.
    exists new. auto.
  - destruct mem as [|ev mem]; [discriminate|]. apply list.Forall_cons in Hregular as [Hev Hmem].
    unfold mbind, st_bind, result_bind in Hrun |- *.
    set (active_roots := filter (λ '(_, time), time < S tmax) roots) in *.
    set (added_roots := filter (λ '(_, time), time = S tmax) roots) in *.
    destruct (TLB.fill_from_btw tid imem fullmem active_roots tmin tmax mem old)
      as [[mid []]|err] eqn:Hprefix; [|discriminate]. cbn in Hrun.
    destruct (TLB.fill_event tid imem fullmem (S tmax) active_roots.*1 ev mid)
      as [[next []]|err] eqn:Hstep; [|discriminate]. cbn in Hrun.
    destruct (IH active_roots mem old new mid Hmem Hvalid Hvalid' Heq Hprefix)
      as [mid' [Hprefix' Heq_mid]].
    pose proof (VMCacheIndexed.fill_from_btw tid imem fullmem active_roots tmin tmax mem
      old mid () Hvalid Hprefix) as Hmid.
    pose proof (VMCacheIndexed.fill_from_btw tid imem fullmem active_roots tmin tmax mem
      new mid' () Hvalid' Hprefix') as Hmid'.
    destruct (fill_event_equiv tid imem fullmem (S tmax) active_roots.*1 ev mid mid' next
      Hev Hmid Hmid' Heq_mid Hstep) as [next' [Hstep' Heq_next]].
    rewrite Hprefix'. cbn. rewrite Hstep'. cbn.
    eapply fill_from_roots_equiv; [exact Heq_next|exact Hrun].
Qed.

End VMCacheEvents.
