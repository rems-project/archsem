(******************************************************************************)
(* Immutable VM translation configuration through cache maintenance          *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMCacheConfig.
Import VMPromising.
Local Notation action A := (stateT TLB.t (result string) A).

Definition config (cache : TLB.t) := (TLB.pte_present cache, TLB.ets cache).
Definition preserves {A} (run : action A) : Prop :=
  ∀ old new ret, run old = Ok (new, ret) → config new = config old.

Lemma preserves_ret {A} (a : A) : preserves (mret a).
Proof.
  intros old new ret Hrun. change (@Ok string _ (old, a) = Ok (new, ret)) in Hrun.
  injection Hrun as <- <-. reflexivity.
Qed.
Lemma preserves_bind {A B} (run : action A) (k : A → action B) :
  preserves run → (∀ a, preserves (k a)) → preserves (run ≫= k).
Proof.
  intros Hrun Htail old new ret Hresult.
  unfold mbind, st_bind, result_bind in Hresult.
  destruct (run old) as [[mid a]|err] eqn:Hfirst; [|discriminate].
  transitivity (config mid); [eapply Htail; exact Hresult|eapply Hrun; exact Hfirst].
Qed.
Lemma preserves_fmap {A B} (run : action A) (f : A → B) :
  preserves run → preserves (f <$> run).
Proof.
  intros Hrun old new ret Hresult.
  unfold fmap, st_fmap, result_fmap in Hresult.
  destruct (run old) as [[mid a]|err] eqn:Hfirst; [|discriminate].
  injection Hresult as <- <-. eapply Hrun. exact Hfirst.
Qed.
Lemma preserves_get {A} (proj : TLB.t → A) : preserves (mget proj).
Proof.
  intros old new ret Hresult.
  change (@Ok string _ (old, proj old) = Ok (new, ret)) in Hresult.
  injection Hresult as <- <-. reflexivity.
Qed.
Lemma preserves_set {A} (proj : TLB.t → A) `{Setter _ _ proj} (f : A → A) :
  (∀ cache, config (set proj f cache) = config cache) → preserves (mset proj f).
Proof.
  intros Hf old new ret Hresult. destruct ret.
  change (@Ok string _ (set proj f old, ()) = Ok (new, ())) in Hresult.
  injection Hresult as <-. apply Hf.
Qed.
Lemma preserves_lift {A} (r : result string A) : preserves (mlift r).
Proof.
  destruct r as [a|err]; intros old new ret Hresult.
  - change (@Ok string _ (old, a) = Ok (new, ret)) in Hresult.
    injection Hresult as <- <-. reflexivity.
  - discriminate.
Qed.
Lemma preserves_throw {A} (err : string) : preserves (mthrow err : action A).
Proof. intros old new ret Hresult. discriminate. Qed.
Lemma preserves_othrow {A} (err : string) (opt : option A) : preserves (othrow err opt).
Proof. destruct opt; [apply preserves_ret|apply preserves_throw]. Qed.
Lemma preserves_guard (err : string) (P : Prop) `{Decision P} : preserves (guard_or err P).
Proof. unfold guard_or. destruct (decide P); [apply preserves_ret|apply preserves_throw]. Qed.
Lemma preserves_guard_unit (err : string) (P : Prop) `{Decision P} : preserves (guard_or' err P).
Proof. unfold guard_or'. apply preserves_bind; [apply preserves_guard|intro; apply preserves_ret]. Qed.
Lemma preserves_mapM {A B} (f : A → action B) xs :
  (∀ a, preserves (f a)) → preserves (mapM f xs).
Proof.
  intro Hf. induction xs as [|a xs IH]; cbn [mapM]; [apply preserves_ret|].
  apply preserves_bind; [apply Hf|]. intro b.
  apply preserves_bind; [exact IH|]. intro bs. apply preserves_ret.
Qed.

Ltac solve_config :=
  first
    [ apply preserves_ret
    | apply preserves_get
    | apply preserves_lift
    | apply preserves_throw
    | apply preserves_othrow
    | apply preserves_guard
    | apply preserves_guard_unit
    | apply preserves_set; intro; reflexivity
    | unfold msetv; apply preserves_set; intro; reflexivity
    | apply preserves_fmap; solve_config
    | apply preserves_bind; [solve_config|intro; solve_config]
    | apply preserves_mapM; intro; solve_config
    | match goal with |- preserves (match ?x with _ => _ end) =>
        destruct x; solve_config end ].

Lemma fill_entry time fe : preserves (TLB.fill_entry time fe).
Proof. unfold TLB.fill_entry. solve_config. Qed.
Lemma fill_root imem mem time roots : preserves (TLB.fill_root imem mem time roots).
Proof. unfold TLB.fill_root, TLB.fill_entry. solve_config. Qed.
Lemma fill_from_entry imem mem time entry : preserves (TLB.fill_from_entry imem mem time entry).
Proof. unfold TLB.fill_from_entry, TLB.fill_entry. solve_config. Qed.
Lemma fill_from_entries_step imem mem time entries : preserves (TLB.fill_from_entries_step imem mem time entries).
Proof.
  unfold TLB.fill_from_entries_step. apply preserves_fmap, preserves_mapM.
  intro entry. apply fill_from_entry.
Qed.
Lemma fill_from_entries imem mem time entries : preserves (TLB.fill_from_entries imem mem time entries).
Proof.
  unfold TLB.fill_from_entries.
  do 3 (apply preserves_bind; [apply fill_from_entries_step|intro]).
  apply preserves_guard_unit.
Qed.
Lemma fill_from_roots imem mem time roots : preserves (TLB.fill_from_roots imem mem time roots).
Proof.
  unfold TLB.fill_from_roots. apply preserves_bind; [apply fill_root|].
  intro entries. apply fill_from_entries.
Qed.
Lemma relevant_entries asids page : preserves (TLB.get_relevant_entries asids page).
Proof. unfold TLB.get_relevant_entries. solve_config. Qed.

Local Opaque TLB.fill_root TLB.fill_from_entry TLB.fill_from_entries
  TLB.fill_from_roots TLB.get_relevant_entries.

Ltac solve_fill_config :=
  first
    [ apply fill_root | apply fill_from_entry | apply fill_from_entries
    | apply fill_from_roots | apply relevant_entries
    | solve_config
    | apply preserves_fmap; solve_fill_config
    | apply preserves_bind; [solve_fill_config|intro; solve_fill_config]
    | apply preserves_mapM; intro; solve_fill_config
    | match goal with |- preserves (match ?x with _ => _ end) =>
        destruct x; solve_fill_config end ].

Lemma fill_write imem mem time roots msg : preserves (TLB.fill_write imem mem time roots msg).
Proof. unfold TLB.fill_write. solve_fill_config. Qed.
Lemma fill_tlbi imem mem time roots tlbi : preserves (TLB.fill_tlbi imem mem time roots tlbi).
Proof. unfold TLB.fill_tlbi. solve_fill_config. Qed.
Lemma fill_event tid imem mem time roots ev : preserves (TLB.fill_event tid imem mem time roots ev).
Proof.
  unfold TLB.fill_event. destruct ev as [msg|tlbi recipient epoch].
  - apply fill_write.
  - destruct (decide (tid = recipient)); [apply fill_tlbi|apply preserves_ret].
Qed.
Lemma fill_promise tid imem mem ev : preserves (TLB.fill_promise tid imem mem ev).
Proof.
  unfold TLB.fill_promise. apply preserves_bind; [apply preserves_get|].
  intro roots. apply fill_event.
Qed.
Lemma fill_from_btw tid imem fullmem roots tmin tmax mem :
  preserves (TLB.fill_from_btw tid imem fullmem roots tmin tmax mem).
Proof.
  revert roots mem. induction tmax as [|tmax IH]; intros roots mem;
    cbn [TLB.fill_from_btw]; destruct (decide (_ < _)); try apply preserves_ret.
  - apply preserves_throw.
  - destruct mem; [apply preserves_throw|].
    apply preserves_bind; [apply IH|]. intro.
    apply preserves_bind; [apply fill_event|]. intro. apply fill_from_roots.
Qed.
Lemma fill_cse tid imem mem time ttbr0 ttbr1 :
  preserves (TLB.fill_cse tid imem mem time ttbr0 ttbr1).
Proof.
  unfold TLB.fill_cse, TLB.roll_back, TLB.fill_from.
  apply preserves_bind; [apply preserves_set; intro; reflexivity|]. intro.
  apply preserves_bind; [unfold msetv; apply preserves_set; intro; reflexivity|]. intro.
  apply fill_from_btw.
Qed.
Lemma fill_asid_root tid imem mem root time :
  preserves (TLB.fill_asid_root tid imem mem root time).
Proof.
  unfold TLB.fill_asid_root, TLB.roll_back, TLB.fill_from.
  apply preserves_bind; [apply preserves_set; intro; reflexivity|]. intro.
  apply preserves_bind; [apply preserves_set; intro; reflexivity|]. intro.
  apply preserves_bind; [apply fill_from_roots|]. intro.
  apply preserves_bind; [apply preserves_get|]. intro. apply fill_from_btw.
Qed.

Theorem emit_promise_ets tid imem mem ev ts ts' :
  TState.emit_promise tid imem mem ev ts = Ok ts' →
  TState.ets2 ts' = TState.ets2 ts ∧ TState.ets3 ts' = TState.ets3 ts.
Proof.
  unfold TState.emit_promise, TState.process_event.
  set (pending := if bool_decide (Ev.tid ev = tid) then
    match ev with
    | Ev.Msg _ => TState.promise_write (length mem) ts
    | _ => TState.promise_tlbi (length mem) ts
    end else ts).
  assert (Hpending : TState.tlb pending = TState.tlb ts).
  { unfold pending. destruct (bool_decide (Ev.tid ev = tid)); [destruct ev|]; reflexivity. }
  unfold TState.run_tlb. rewrite Hpending.
  destruct (TState.tlb ts) as [old|] eqn:Hcache.
  - destruct (TLB.fill_promise tid imem mem ev old) as [[new []]|err] eqn:Hfill;
      cbn; [|discriminate].
    injection 1 as <-.
    pose proof (fill_promise tid imem mem ev old new () Hfill) as Hconfig.
    unfold config in Hconfig. injection Hconfig as _ Hets.
    unfold TState.ets2, TState.ets3.
    change (TState.tlb (setv TState.tlb (Some new) pending)) with (Some new).
    rewrite Hcache. cbn. rewrite Hets. auto.
  - injection 1 as <-. unfold TState.ets2, TState.ets3. rewrite Hpending, Hcache. auto.
Qed.
End VMCacheConfig.
