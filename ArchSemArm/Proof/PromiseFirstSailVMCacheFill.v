(******************************************************************************)
(* Actual TLB fill operations preserve earlier entry histories                 *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCache PromiseFirstConcreteCurrent.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMCacheFillReplay.
Import VMPromising VMCacheReplay.
#[local] Existing Instance TLB.Decision_affects.
Local Notation action A := (stateT TLB.t (result string) A).

Definition preserves {A} (bound : nat) (run : action A) : Prop :=
  ∀ old new ret, run old = Ok (new, ret) → extends bound (TLB.vatlb old) (TLB.vatlb new).

Lemma preserves_ret {A} bound (a : A) : preserves bound (mret a).
Proof.
  intros old new ret Hrun. change (@Ok string _ (old, a) = Ok (new, ret)) in Hrun.
  injection Hrun as <- <-. apply extends_refl.
Qed.

Lemma preserves_bind {A B} bound (run : action A) (k : A → action B) :
  preserves bound run → (∀ a, preserves bound (k a)) → preserves bound (run ≫= k).
Proof.
  intros Hrun Htail old new ret Hresult.
  unfold mbind, st_bind, result_bind in Hresult.
  destruct (run old) as [[mid a]|err] eqn:Hfirst; [|discriminate].
  eapply extends_trans; [eapply Hrun; exact Hfirst|eapply Htail; exact Hresult].
Qed.

Lemma preserves_fmap {A B} bound (run : action A) (f : A → B) :
  preserves bound run → preserves bound (f <$> run).
Proof.
  intros Hrun old new ret Hresult.
  unfold fmap, st_fmap, result_fmap in Hresult.
  destruct (run old) as [[mid a]|err] eqn:Hfirst; [|discriminate].
  injection Hresult as <- <-. eapply Hrun. exact Hfirst.
Qed.

Lemma preserves_get {A} bound (proj : TLB.t → A) : preserves bound (mget proj).
Proof.
  intros old new ret Hresult.
  change (@Ok string _ (old, proj old) = Ok (new, ret)) in Hresult.
  injection Hresult as <- <-. apply extends_refl.
Qed.

Lemma preserves_lift {A} bound (r : result string A) : preserves bound (mlift r).
Proof.
  destruct r as [a|err]; intros old new ret Hresult.
  - change (@Ok string _ (old, a) = Ok (new, ret)) in Hresult.
    injection Hresult as <- <-. apply extends_refl.
  - discriminate.
Qed.

Lemma preserves_throw {A} bound (err : string) : preserves bound (mthrow err : action A).
Proof. intros old new ret Hresult. discriminate. Qed.

Lemma preserves_othrow {A} bound (err : string) (opt : option A) : preserves bound (othrow err opt).
Proof. destruct opt; [apply preserves_ret|apply preserves_throw]. Qed.

Lemma preserves_guard bound (err : string) (P : Prop) `{Decision P} : preserves bound (guard_or err P).
Proof. unfold guard_or. destruct (decide P); [apply preserves_ret|apply preserves_throw]. Qed.

Lemma preserves_guard_unit bound (err : string) (P : Prop) `{Decision P} : preserves bound (guard_or' err P).
Proof. unfold guard_or'. apply preserves_bind; [apply preserves_guard|intro; apply preserves_ret]. Qed.

Lemma preserves_mapM {A B} bound (f : A → action B) xs :
  (∀ a, preserves bound (f a)) → preserves bound (mapM f xs).
Proof.
  intro Hf. induction xs as [|a xs IH]; cbn [mapM]; [apply preserves_ret|].
  apply preserves_bind; [apply Hf|]. intro b.
  apply preserves_bind; [exact IH|]. intro bs. apply preserves_ret.
Qed.

Lemma preserves_fill_entry bound time fe :
  bound < time → preserves bound (TLB.fill_entry time fe).
Proof. intros Htime old new ret Hrun. eapply fill_entry_extends; eassumption. Qed.

Ltac solve_preserves :=
  first
    [ apply preserves_ret
    | apply preserves_get
    | apply preserves_lift
    | apply preserves_throw
    | apply preserves_othrow
    | apply preserves_guard
    | apply preserves_guard_unit
    | apply preserves_fill_entry; assumption
    | apply preserves_fmap; solve_preserves
    | apply preserves_bind; [solve_preserves|intro; solve_preserves]
    | apply preserves_mapM; intro; solve_preserves
    | match goal with |- preserves _ (match ?x with _ => _ end) =>
        destruct x; solve_preserves end ].

Lemma preserves_fill_root bound imem mem time roots :
  bound < time → preserves bound (TLB.fill_root imem mem time roots).
Proof.
  intro Htime. unfold TLB.fill_root. solve_preserves.
Qed.

Lemma preserves_fill_from_entry bound imem mem time entry :
  bound < time → preserves bound (TLB.fill_from_entry imem mem time entry).
Proof.
  intro Htime. unfold TLB.fill_from_entry. solve_preserves.
Qed.

Lemma preserves_fill_from_entries_step bound imem mem time entries :
  bound < time → preserves bound (TLB.fill_from_entries_step imem mem time entries).
Proof.
  intro Htime. unfold TLB.fill_from_entries_step.
  apply preserves_fmap, preserves_mapM. intro entry.
  apply preserves_fill_from_entry, Htime.
Qed.

Lemma preserves_fill_from_entries bound imem mem time entries :
  bound < time → preserves bound (TLB.fill_from_entries imem mem time entries).
Proof.
  intro Htime. unfold TLB.fill_from_entries.
  do 3 (apply preserves_bind; [apply preserves_fill_from_entries_step, Htime|intro]).
  apply preserves_guard_unit.
Qed.

Lemma preserves_fill_full bound imem mem time roots :
  bound < time → preserves bound (TLB.fill_full imem mem time roots).
Proof.
  intro Htime. unfold TLB.fill_full.
  apply preserves_bind; [apply preserves_fill_root, Htime|].
  intro entries. apply preserves_fill_from_entries, Htime.
Qed.
Lemma preserves_vatlb bound (f : TLB.VATLB.t → TLB.VATLB.t) :
  (∀ cache, extends bound cache (f cache)) → preserves bound (mset TLB.vatlb f).
Proof.
  intros Hf old new ret Hrun. destruct ret.
  change (@Ok string _ (set TLB.vatlb f old, ()) = Ok (new, ())) in Hrun.
  injection Hrun as <-. apply Hf.
Qed.

Lemma preserves_relevant_entries bound asids page :
  preserves bound (TLB.get_relevant_entries asids page).
Proof. unfold TLB.get_relevant_entries. solve_preserves. Qed.

Lemma preserves_tlbi_marker bound time issuer fe :
  bound < time → preserves bound (mset TLB.vatlb (alter ((TLB.Entry.Tlbi issuer, time)::.) fe)).
Proof.
  intro Htime. apply preserves_vatlb. intro cache.
  unfold alter, alter_default. apply update_entry_extends.
  intros events Hlookup. exists [(TLB.Entry.Tlbi issuer, time)].
  split; [constructor; [exact Htime|constructor]|reflexivity].
Qed.

Lemma preserves_invalidate_all bound time tlbi :
  bound < time → preserves bound (mset TLB.vatlb (TLB.VATLB.map_fe
    (λ fe events, if decide (TLB.affects tlbi fe)
      then (TLB.Entry.Tlbi (TLBI.tid tlbi), time) :: events else events))).
Proof. intro Htime. apply preserves_vatlb. intro cache. apply invalidate_all_extends, Htime. Qed.

Ltac solve_fill_preserves :=
  first
    [ apply preserves_fill_root; assumption
    | apply preserves_fill_from_entry; assumption
    | apply preserves_fill_from_entries; assumption
    | apply preserves_fill_full; assumption
    | apply preserves_tlbi_marker; assumption
    | apply preserves_invalidate_all; assumption
    | apply preserves_relevant_entries
    | solve_preserves
    | apply preserves_fmap; solve_fill_preserves
    | apply preserves_bind; [solve_fill_preserves|intro; solve_fill_preserves]
    | apply preserves_mapM; intro; solve_fill_preserves
    | match goal with |- preserves _ (match ?x with _ => _ end) =>
        destruct x; solve_fill_preserves end ].

Lemma preserves_fill_write bound imem mem time roots msg :
  bound < time → preserves bound (TLB.fill_write imem mem time roots msg).
Proof. intro Htime. unfold TLB.fill_write. solve_fill_preserves. Qed.

Lemma preserves_fill_tlbi bound imem mem time roots tlbi :
  bound < time → preserves bound (TLB.fill_tlbi imem mem time roots tlbi).
Proof. intro Htime. unfold TLB.fill_tlbi. solve_fill_preserves. Qed.

Theorem fill_event_extends bound tid imem mem time roots ev old new :
  bound < time → TLB.fill_event tid imem mem time roots ev old = Ok (new, ()) →
  extends bound (TLB.vatlb old) (TLB.vatlb new).
Proof.
  intro Htime. assert (Hpres : preserves bound (TLB.fill_event tid imem mem time roots ev)); [|intro Hrun; exact (Hpres old new () Hrun)].
  unfold TLB.fill_event. destruct ev as [msg|tlbi recipient].
  - apply preserves_fill_write, Htime.
  - destruct (decide (tid = recipient)); [apply preserves_fill_tlbi, Htime|apply preserves_ret].
Qed.

Theorem fill_promise_extends tid imem mem ev old new :
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (new, ()) →
  extends (length mem) (TLB.vatlb old) (TLB.vatlb new).
Proof.
  assert (Hpres : preserves (length mem) (TLB.fill_promise tid imem (ev :: mem) ev)); [|intro Hrun; exact (Hpres old new () Hrun)].
  unfold TLB.fill_promise. apply preserves_bind; [apply preserves_get|].
  intro roots. intros before after ret Hfill. destruct ret.
  eapply fill_event_extends; [|exact Hfill]. cbn. lia.
Qed.
Theorem emit_promise_cache_extends tid imem mem ev ts ts' old :
  TState.tlb ts = Some old →
  TState.emit_promise tid imem (ev :: mem) ev ts = Ok ts' →
  ∃ new, TState.tlb ts' = Some new ∧
    extends (length mem) (TLB.vatlb old) (TLB.vatlb new).
Proof.
  intros Hcache Hpromise.
  set (pending := if bool_decide (Ev.tid ev = tid) then
    match ev with
    | Ev.Msg _ => TState.promise_write (length (ev :: mem)) ts
    | _ => TState.promise_tlbi (length (ev :: mem)) ts
    end else ts).
  assert (Hpending : TState.tlb pending = Some old).
  { unfold pending. destruct (bool_decide (Ev.tid ev = tid)); [destruct ev|]; exact Hcache. }
  change (TState.run_tlb (TLB.fill_promise tid imem (ev :: mem) ev) pending = Ok ts') in Hpromise.
  unfold TState.run_tlb in Hpromise. rewrite Hpending in Hpromise.
  destruct (TLB.fill_promise tid imem (ev :: mem) ev old) as [[new []]|err] eqn:Hfill;
    cbn in Hpromise; [|discriminate].
  injection Hpromise as <-. exists new. split; [reflexivity|].
  eapply fill_promise_extends. exact Hfill.
Qed.
End VMCacheFillReplay.

#[local] Typeclasses Transparent VMPromising.VMPromising Promising.mEvent Promising.tState.
#[local] Typeclasses Transparent VMPromising.Memory.t.

Theorem VMSail_global_promise_cache_extends bbm {n} (tid : fin n) st next ev old :
  PState.promise (VMPromising.VMPromising bbm) ev st = Ok next →
  VMPromising.TState.tlb (PState.tstate tid st) = Some old →
  ∃ new, VMPromising.TState.tlb (PState.tstate tid next) = Some new ∧
    VMCacheReplay.extends (length (PState.events st))
      (VMPromising.TLB.vatlb old) (VMPromising.TLB.vatlb new).
Proof.
  intros Hpromise Hcache.
  destruct (VMPromising_promise_success ev st next Hpromise) as [_ [_ Hstates]].
  eapply VMCacheFillReplay.emit_promise_cache_extends; [exact Hcache|exact (Hstates tid)].
Qed.
