(******************************************************************************)
(* Replaying cache maintenance over an extended shared history                *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheConfig.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMCacheRoots.
Import VMPromising.
Local Notation action A := (stateT TLB.t (result string) A).

Definition config := TLB.asid_roots.
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
End VMCacheRoots.

Module VMCacheHistory.
Import VMPromising.
Local Notation action A := (stateT TLB.t (result string) A).

Lemma read_word_future addr imem mem ev time :
  time ≤ length mem →
  Memory.read_word addr imem (ev :: mem) time = Memory.read_word addr imem mem time.
Proof.
  intro Htime. unfold Memory.read_word, PromMemory.read_word, PromMemory.read_from.
  rewrite PromMemory.cut_before_cons_old by exact Htime. reflexivity.
Qed.

Lemma fill_root_future imem mem ev time roots :
  time ≤ length mem →
  TLB.fill_root imem (ev :: mem) time roots = TLB.fill_root imem mem time roots.
Proof.
  intro Htime. unfold TLB.fill_root.
  f_equal. f_equal. extensionality root. destruct root as [[asid ttbr] upper].
  f_equal. extensionality indexes. f_equal. f_equal. extensionality idx.
  rewrite read_word_future by exact Htime. reflexivity.
Qed.

Lemma fill_from_entry_future imem mem ev time entry :
  time ≤ length mem →
  TLB.fill_from_entry imem (ev :: mem) time entry =
    TLB.fill_from_entry imem mem time entry.
Proof.
  intro Htime. unfold TLB.fill_from_entry.
  f_equal. extensionality checked. f_equal. extensionality indexes.
  f_equal. extensionality lvl. f_equal. f_equal. extensionality idx.
  rewrite read_word_future by exact Htime. reflexivity.
Qed.

Lemma fill_from_entries_step_future imem mem ev time entries :
  time ≤ length mem →
  TLB.fill_from_entries_step imem (ev :: mem) time entries =
    TLB.fill_from_entries_step imem mem time entries.
Proof.
  intro Htime. unfold TLB.fill_from_entries_step.
  f_equal. f_equal. extensionality entry. apply fill_from_entry_future, Htime.
Qed.

Lemma fill_from_entries_future imem mem ev time entries :
  time ≤ length mem →
  TLB.fill_from_entries imem (ev :: mem) time entries =
    TLB.fill_from_entries imem mem time entries.
Proof.
  intro Htime. unfold TLB.fill_from_entries.
  rewrite fill_from_entries_step_future by exact Htime.
  f_equal. extensionality es.
  rewrite fill_from_entries_step_future by exact Htime.
  f_equal. extensionality es'.
  rewrite fill_from_entries_step_future by exact Htime. reflexivity.
Qed.

Lemma fill_from_roots_future imem mem ev time roots :
  time ≤ length mem →
  TLB.fill_from_roots imem (ev :: mem) time roots =
    TLB.fill_from_roots imem mem time roots.
Proof.
  intro Htime. unfold TLB.fill_from_roots.
  rewrite fill_root_future by exact Htime.
  f_equal. extensionality entries. apply fill_from_entries_future, Htime.
Qed.

Lemma fill_write_future imem mem ev time roots msg :
  time ≤ length mem →
  TLB.fill_write imem (ev :: mem) time roots msg =
    TLB.fill_write imem mem time roots msg.
Proof.
  intro Htime. unfold TLB.fill_write.
  f_equal. extensionality checked. rewrite fill_root_future by exact Htime.
  f_equal. extensionality entries. f_equal. extensionality relevant.
  apply fill_from_entries_future, Htime.
Qed.

Lemma fill_tlbi_future imem mem ev time roots tlbi :
  time ≤ length mem →
  TLB.fill_tlbi imem (ev :: mem) time roots tlbi =
    TLB.fill_tlbi imem mem time roots tlbi.
Proof.
  intro Htime. unfold TLB.fill_tlbi. destruct (TLBI.last tlbi).
  - f_equal. extensionality cache. f_equal. extensionality entries.
    f_equal. extensionality parents. apply fill_from_entries_future, Htime.
  - f_equal. extensionality checked. apply fill_from_roots_future, Htime.
Qed.

Lemma fill_event_future tid imem mem future time roots ev :
  time ≤ length mem →
  TLB.fill_event tid imem (future :: mem) time roots ev =
    TLB.fill_event tid imem mem time roots ev.
Proof.
  intro Htime. unfold TLB.fill_event. destruct ev as [msg|tlbi recipient epoch].
  - apply fill_write_future, Htime.
  - destruct (decide (tid = recipient)); [apply fill_tlbi_future, Htime|reflexivity].
Qed.

Lemma fill_from_btw_future tid imem mem ev roots tmin tmax history :
  tmax ≤ length mem →
  TLB.fill_from_btw tid imem (ev :: mem) roots tmin tmax history =
    TLB.fill_from_btw tid imem mem roots tmin tmax history.
Proof.
  revert roots history. induction tmax as [|tmax IH]; intros roots history Htime;
    cbn [TLB.fill_from_btw]; destruct (decide (_ < _)); try reflexivity.
  destruct history; [reflexivity|].
  rewrite IH by lia. f_equal. extensionality checked.
  rewrite fill_event_future by lia. f_equal. extensionality checked'.
  apply fill_from_roots_future. lia.
Qed.

Lemma fill_from_roots_nil imem mem time :
  TLB.fill_from_roots imem mem time [] = (mret () : action ()).
Proof. reflexivity. Qed.

Lemma fill_from_future tid imem mem ev roots time :
  time ≤ length mem → Forall (λ root, root.2 ≤ length mem) roots →
  TLB.fill_from tid imem (ev :: mem) roots (S time) =
    (TLB.fill_from tid imem mem roots (S time);;
      TLB.fill_event tid imem (ev :: mem) (S (length mem)) roots.*1 ev).
Proof.
  intros Htime Hroots. unfold TLB.fill_from. cbn [length TLB.fill_from_btw].
  rewrite decide_False by lia.
  assert (Hactive : filter (λ '(_, stamp), stamp < S (length mem)) roots = roots).
  { induction Hroots as [|root roots Hroot Hroots IH]; [reflexivity|].
    destruct root as [root stamp]. cbn in Hroot. rewrite filter_cons, decide_True by lia. f_equal. exact IH. }
  assert (Hadded : filter (λ '(_, stamp), stamp = S (length mem)) roots = []).
  { clear Hactive. induction Hroots as [|root roots Hroot Hroots IH]; [reflexivity|].
    destruct root as [root stamp]. cbn in Hroot. rewrite filter_cons, decide_False by lia. exact IH. }
  rewrite Hactive, Hadded, fill_from_btw_future by lia.
  cbn [fmap list_fmap]. rewrite fill_from_roots_nil.
  f_equal. extensionality checked. extensionality cache.
  unfold mbind, st_bind, mret, st_ret, result_bind, result_ret.
  destruct (TLB.fill_event tid imem (ev :: mem) (S (length mem)) roots.*1 ev cache)
    as [[next []]|err]; reflexivity.
Qed.

(** The suffix after an old CSE is rebuilt using exactly the new context.
    The last event can be processed separately after replaying the old history. *)
Theorem fill_cse_future tid imem mem ev time ttbr0 ttbr1 :
  time ≤ length mem →
  let roots := if ttbr1 is Some ttbr1
    then [(bv_extract 48 16 ttbr0, ttbr0, false, time);
          (bv_extract 48 16 ttbr0, ttbr1, true, time)]
    else [(bv_extract 48 16 ttbr0, ttbr0, false, time)] in
  TLB.fill_cse tid imem (ev :: mem) time ttbr0 ttbr1 =
    (TLB.fill_cse tid imem mem time ttbr0 ttbr1;;
      TLB.fill_event tid imem (ev :: mem) (S (length mem)) roots.*1 ev).
Proof.
  intro Htime. cbn zeta. unfold TLB.fill_cse.
  rewrite fill_from_future by (try exact Htime; destruct ttbr1; repeat constructor; exact Htime).
  extensionality cache. reflexivity.
Qed.

(** Adding a TTBR root and rebuilding its suffix also factors at the end of
    the former history. This requires every previously active root to be old. *)
Theorem fill_asid_root_future tid imem mem ev root time cache :
  time ≤ length mem →
  Forall (λ entry, entry.2 ≤ length mem) (TLB.asid_roots cache) →
  TLB.fill_asid_root tid imem (ev :: mem) root time cache =
    (TLB.fill_asid_root tid imem mem root time;;
      TLB.fill_event tid imem (ev :: mem) (S (length mem))
        (root :: (TLB.asid_roots cache).*1) ev) cache.
Proof.
  intros Htime Hroots. unfold TLB.fill_asid_root.
  rewrite fill_from_roots_future by exact Htime.
  set (start := set TLB.asid_roots (cons (root, time))
    (set TLB.vatlb (TLB.VATLB.map_fe
      (λ _, filter (λ '(_, stamp), stamp ≤ time))) cache)).
  change ((TLB.fill_from_roots imem mem time [root] start ≫=
    λ '(mid, _), TLB.fill_from tid imem (ev :: mem) (TLB.asid_roots mid) (S time) mid) =
    ((TLB.fill_from_roots imem mem time [root] start ≫=
      λ '(mid, _), TLB.fill_from tid imem mem (TLB.asid_roots mid) (S time) mid) ≫=
      λ '(next, _), TLB.fill_event tid imem (ev :: mem) (S (length mem))
        (root :: (TLB.asid_roots cache).*1) ev next)).
  destruct (TLB.fill_from_roots imem mem time [root] start) as [[mid []]|err] eqn:Hfill;
    [|reflexivity].
  pose proof (VMCacheRoots.fill_from_roots imem mem time [root] start mid () Hfill) as Hsame.
  unfold VMCacheRoots.config in Hsame. subst start. cbn in Hsame.
  cbn [mbind result_bind]. rewrite Hsame.
  rewrite fill_from_future by (try exact Htime; constructor; assumption).
  reflexivity.
Qed.

Lemma fill_cse_roots tid imem mem time ttbr0 ttbr1 cache next :
  TLB.fill_cse tid imem mem time ttbr0 ttbr1 cache = Ok (next, ()) →
  TLB.asid_roots next = if ttbr1 is Some ttbr1
    then [(bv_extract 48 16 ttbr0, ttbr0, false, time);
          (bv_extract 48 16 ttbr0, ttbr1, true, time)]
    else [(bv_extract 48 16 ttbr0, ttbr0, false, time)].
Proof.
  intro Hrun. unfold TLB.fill_cse in Hrun.
  set (roots := if ttbr1 is Some ttbr1
    then [(bv_extract 48 16 ttbr0, ttbr0, false, time);
          (bv_extract 48 16 ttbr0, ttbr1, true, time)]
    else [(bv_extract 48 16 ttbr0, ttbr0, false, time)]) in *.
  change (TLB.fill_from tid imem mem roots (S time)
    (setv TLB.asid_roots roots (set TLB.vatlb (TLB.VATLB.map_fe
      (λ _, filter (λ '(_, stamp), stamp ≤ time))) cache)) = Ok (next, ())) in Hrun.
  exact (VMCacheRoots.fill_from_btw tid imem mem roots (S time) (length mem) mem
    _ next () Hrun).
Qed.

Corollary fill_cse_future_promise tid imem mem ev time ttbr0 ttbr1 cache next :
  time ≤ length mem →
  TLB.fill_cse tid imem mem time ttbr0 ttbr1 cache = Ok (next, ()) →
  TLB.fill_cse tid imem (ev :: mem) time ttbr0 ttbr1 cache =
    TLB.fill_promise tid imem (ev :: mem) ev next.
Proof.
  intros Htime Hrun. rewrite fill_cse_future by exact Htime.
  unfold mbind, st_bind, result_bind. rewrite Hrun.
  pose proof (fill_cse_roots tid imem mem time ttbr0 ttbr1 cache next Hrun) as Hroots.
  unfold TLB.fill_promise.
  change (TLB.fill_event tid imem (ev :: mem) (S (length mem))
    (if ttbr1 is Some ttbr1
     then [(bv_extract 48 16 ttbr0, ttbr0, false, time);
           (bv_extract 48 16 ttbr0, ttbr1, true, time)]
     else [(bv_extract 48 16 ttbr0, ttbr0, false, time)]).*1 ev next =
    TLB.fill_event tid imem (ev :: mem) (S (length mem)) (TLB.asid_roots next).*1 ev next).
  rewrite Hroots. reflexivity.
Qed.

End VMCacheHistory.
