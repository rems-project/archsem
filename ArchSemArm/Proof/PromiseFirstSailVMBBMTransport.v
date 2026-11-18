(******************************************************************************)
(* Final BBM validation across caches with equal entry histories              *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMBBM PromiseFirstSailVMCacheRefill
  PromiseFirstSailVMCacheExchange PromiseFirstSailVMCacheOrder.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMBBMTransport.
Import VMPromising.
#[local] Typeclasses Transparent BBM.GDesc.

(** At a tied timestamp, the interval traversal may consume a different
    history after swapping the arguments. The zero clamp needs its own case. *)
Lemma intervals_cons bound event1 stamp1 rest1 event2 stamp2 rest2 :
  BBM.time_intervals bound ((event1, stamp1) :: rest1) ((event2, stamp2) :: rest2) =
    let pop1 := BBM.time_intervals (min bound (Nat.pred stamp1)) rest1 ((event2, stamp2) :: rest2) in
    let pop2 := BBM.time_intervals (min bound (Nat.pred stamp2)) ((event1, stamp1) :: rest1) rest2 in
    match event1, event2 with
    | TLB.Entry.Load, TLB.Entry.Load =>
        let rest := if decide (stamp2 ≤ stamp1) then pop1 else pop2 in
        if decide (max stamp1 stamp2 ≤ bound) then (max stamp1 stamp2, bound) :: rest else rest
    | TLB.Entry.Load, _ => if decide (stamp2 ≤ stamp1) then pop1 else pop2
    | _, _ => if decide (stamp2 < stamp1) then pop1 else pop2
    end.
Proof. reflexivity. Qed.

Lemma intervals_tlbi_zero_l bound tid rest events :
  BBM.time_intervals bound ((TLB.Entry.Tlbi tid, 0) :: rest) events = [].
Proof.
  revert bound. induction events as [|[event stamp] events IH]; intro bound.
  - reflexivity.
  - rewrite intervals_cons. cbn beta iota zeta. rewrite decide_False by lia. apply IH.
Qed.

Definition before top (events : TLB.Entry.events) := filter (λ event, event.2 < top) events.

Lemma intervals_before top bound events1 events2 :
  bound < top → VMCacheOrder.bounded top events1 → VMCacheOrder.bounded top events2 →
  BBM.time_intervals bound events1 events2 =
    BBM.time_intervals bound (before top events1) (before top events2).
Proof.
  revert bound events2. induction events1 as [|[event1 stamp1] rest1 IH1];
    intros bound events2 Hbound Hfirst Hsecond; [reflexivity|].
  revert bound Hbound Hsecond. induction events2 as [|[event2 stamp2] rest2 IH2];
    intros bound Hbound Hsecond.
  - rewrite VMBBMReplay.time_intervals_nil_r, VMBBMReplay.time_intervals_nil_r. reflexivity.
  - apply Forall_cons_1 in Hfirst as [Hstamp1 Hrest1].
    apply Forall_cons_1 in Hsecond as [Hstamp2 Hrest2]. cbn in Hstamp1, Hstamp2.
    assert (Hfirst : VMCacheOrder.bounded top ((event1, stamp1) :: rest1)) by (constructor; assumption).
    assert (Hsecond : VMCacheOrder.bounded top ((event2, stamp2) :: rest2)) by (constructor; assumption).
    unfold before at 1 2. rewrite !filter_cons. cbn [snd].
    destruct (decide (stamp1 < top)) as [Hlt1|Htop1];
      destruct (decide (stamp2 < top)) as [Hlt2|Htop2].
    + change (BBM.time_intervals bound ((event1, stamp1) :: rest1) ((event2, stamp2) :: rest2) =
        BBM.time_intervals bound ((event1, stamp1) :: before top rest1) ((event2, stamp2) :: before top rest2)).
      rewrite !intervals_cons. cbn beta iota zeta.
      rewrite (IH1 (min bound (Nat.pred stamp1)) _ ltac:(lia) Hrest1 Hsecond),
        (IH2 (min bound (Nat.pred stamp2)) ltac:(lia) Hrest2).
      unfold before. rewrite !filter_cons. cbn [snd].
      rewrite (decide_True (P := stamp1 < top)), (decide_True (P := stamp2 < top)) by assumption.
      reflexivity.
    + assert (stamp2 = top) by lia. subst stamp2.
      rewrite intervals_cons. cbn beta iota zeta. destruct event1, event2;
        rewrite ?decide_False by lia;
        replace (min bound (Nat.pred top)) with bound by lia;
        rewrite (IH2 bound Hbound Hrest2); unfold before; rewrite filter_cons; cbn [snd];
        rewrite decide_True by assumption; reflexivity.
    + assert (stamp1 = top) by lia. subst stamp1.
      rewrite intervals_cons. cbn beta iota zeta. destruct event1, event2;
        repeat first [(rewrite decide_True by lia) | (rewrite decide_False by lia)];
        replace (min bound (Nat.pred top)) with bound by lia;
        rewrite (IH1 bound _ Hbound Hrest1 Hsecond); unfold before; rewrite filter_cons; cbn [snd];
        repeat first [(rewrite decide_True by lia) | (rewrite decide_False by lia)]; reflexivity.
    + assert (stamp1 = top ∧ stamp2 = top) as [-> ->] by lia.
      rewrite intervals_cons. cbn beta iota zeta. destruct event1, event2;
        repeat first [(rewrite decide_True by lia) | (rewrite decide_False by lia)];
        replace (min bound (Nat.pred top)) with bound by lia.
      all: first [rewrite (IH1 _ _ Hbound Hrest1 Hsecond) | rewrite (IH2 _ Hbound Hrest2)];
        unfold before; rewrite filter_cons; cbn [snd]; rewrite decide_False by lia; reflexivity.
Qed.

Lemma intervals_late_l top bound event rest events :
  bound < top → VMCacheOrder.bounded top rest → VMCacheOrder.bounded top events →
  BBM.time_intervals bound ((event, top) :: rest) events = BBM.time_intervals bound rest events.
Proof.
  intros Hlt Hrest Hevents.
  rewrite (intervals_before top bound ((event, top) :: rest) events);
    [|exact Hlt|constructor; [cbn; lia|exact Hrest]|exact Hevents].
  rewrite (intervals_before top bound rest events) by assumption.
  unfold before. rewrite filter_cons. cbn [snd]. rewrite decide_False by lia. reflexivity.
Qed.

Lemma intervals_load_tie bound stamp rest other :
  VMCacheOrder.ordered ((TLB.Entry.Load, stamp) :: rest) →
  BBM.time_intervals (min bound (Nat.pred stamp)) rest ((TLB.Entry.Load, stamp) :: other) =
    BBM.time_intervals (min bound (Nat.pred stamp)) rest other.
Proof.
  destruct rest as [|[event time] rest]; intro Hordered; [reflexivity|].
  destruct Hordered as [[Hle Hload] Hrest]. destruct event; [exfalso; apply Hload; auto|].
  rewrite intervals_cons. cbn beta iota zeta. rewrite decide_False by lia.
  replace (min (min bound (Nat.pred stamp)) (Nat.pred stamp)) with (min bound (Nat.pred stamp)) by lia.
  reflexivity.
Qed.

Theorem time_intervals_sym bound events1 events2 :
  VMCacheOrder.ordered events1 → VMCacheOrder.ordered events2 →
  BBM.time_intervals bound events1 events2 = BBM.time_intervals bound events2 events1.
Proof.
  revert bound events2. induction events1 as [|[event1 stamp1] rest1 IH1];
    intros bound events2 Hfirst Hsecond.
  - rewrite VMBBMReplay.time_intervals_nil_r. reflexivity.
  - revert bound Hsecond. induction events2 as [|[event2 stamp2] rest2 IH2]; intros bound Hsecond.
    + rewrite VMBBMReplay.time_intervals_nil_r. reflexivity.
    + pose proof (proj2 Hfirst) as Hrest1. pose proof (proj2 Hsecond) as Hrest2.
      pose proof (VMCacheOrder.ordered_head_bound _ _ _ Hfirst) as Hbound1.
      pose proof (VMCacheOrder.ordered_head_bound _ _ _ Hsecond) as Hbound2.
      destruct event1, event2.
      * destruct (Nat.eq_dec stamp1 stamp2) as [->|Hne].
        -- rewrite !intervals_cons. cbn beta iota zeta.
           rewrite !(decide_True (P := stamp2 ≤ stamp2)) by lia.
           rewrite (intervals_load_tie _ _ _ _ Hfirst), (intervals_load_tie _ _ _ _ Hsecond).
           rewrite IH1 by assumption. reflexivity.
        -- rewrite !intervals_cons. cbn beta iota zeta.
           replace (max stamp2 stamp1) with (max stamp1 stamp2) by lia.
           repeat case_decide; try lia; try (rewrite IH1 by assumption; reflexivity);
             try (rewrite IH2 by assumption; reflexivity).
      * rewrite !intervals_cons. cbn beta iota zeta.
        repeat case_decide; try lia; try (rewrite IH1 by assumption; reflexivity);
          try (rewrite IH2 by assumption; reflexivity).
      * rewrite !intervals_cons. cbn beta iota zeta.
        repeat case_decide; try lia; try (rewrite IH1 by assumption; reflexivity);
          try (rewrite IH2 by assumption; reflexivity).
      * destruct (Nat.eq_dec stamp1 stamp2) as [->|Hne].
        -- destruct stamp2 as [|stamp].
           ++ rewrite !intervals_tlbi_zero_l. reflexivity.
           ++ rewrite !intervals_cons. cbn beta iota zeta.
              rewrite !decide_False by lia. cbn [Nat.pred].
              rewrite !intervals_late_l by (try assumption; lia).
              apply IH1; assumption.
        -- rewrite !intervals_cons. cbn beta iota zeta.
           repeat case_decide; try lia; try (rewrite IH1 by assumption; reflexivity);
             try (rewrite IH2 by assumption; reflexivity).
Qed.

(** Successful checks can be reordered even when failing checks return
    different error messages. *)
Definition all_ok {A} (f : A → result string bool) xs := List.forallb id <$> mapM f xs.

Lemma all_ok_cons {A} (f : A → result string bool) x xs :
  all_ok f (x :: xs) = (b ← f x; rest ← all_ok f xs; mret (b && rest)).
Proof.
  unfold all_ok. cbn [mapM]. unfold mbind, result_bind, fmap, result_fmap, mret, result_ret.
  destruct (f x); [destruct (mapM f xs); reflexivity|reflexivity].
Qed.

Lemma all_ok_cons_true {A} (f : A → result string bool) x xs :
  all_ok f (x :: xs) = Ok true ↔ f x = Ok true ∧ all_ok f xs = Ok true.
Proof.
  rewrite all_ok_cons. unfold mbind, result_bind, mret, result_ret.
  destruct (f x) as [[]|err], (all_ok f xs) as [[]|err']; cbn; intuition congruence.
Qed.

Lemma all_ok_true {A} (f : A → result string bool) xs :
  all_ok f xs = Ok true ↔ ∀ x, x ∈ xs → f x = Ok true.
Proof.
  induction xs as [|x xs IH].
  - split; [intros _ y Hin; inversion Hin|intros _; reflexivity].
  - etrans; [apply all_ok_cons_true|]. split.
    + intros [Hx Hxs] y Hin. apply elem_of_cons in Hin as [->|Hin]; [exact Hx|].
      exact (proj1 IH Hxs y Hin).
    + intro H. split; [apply H; left|apply IH; intros y Hin; apply H; right; exact Hin].
Qed.

Lemma negb_ok_false (r : result string bool) : negb <$> r = Ok true ↔ r = Ok false.
Proof. destruct r as [[]|err]; cbn; intuition congruence. Qed.

Lemma negb_ok_true (r : result string bool) : negb <$> r = Ok false ↔ r = Ok true.
Proof. destruct r as [[]|err]; cbn; intuition congruence. Qed.

Lemma pairs_cons_true {A} (f : A → A → result string bool) x xs :
  BBM.for_all_pairs f (x :: xs) = Ok true ↔
    all_ok (f x) xs = Ok true ∧ BBM.for_all_pairs f xs = Ok true.
Proof.
  change ((b ← all_ok (f x) xs; if (b : bool) then BBM.for_all_pairs f xs else Ok false) = Ok true ↔
    all_ok (f x) xs = Ok true ∧ BBM.for_all_pairs f xs = Ok true).
  unfold mbind, result_bind.
  destruct (all_ok (f x) xs) as [[]|err], (BBM.for_all_pairs f xs) as [[]|err'];
    cbn; intuition congruence.
Qed.

Lemma all_ok_perm {A} (f : A → result string bool) xs ys :
  Permutation xs ys → all_ok f xs = Ok true → all_ok f ys = Ok true.
Proof.
  intros Hperm Hxs. apply all_ok_true.
  intros x Hin. apply (proj1 (all_ok_true f xs) Hxs). apply list_elem_of_In. eapply Permutation_in;
    [apply Permutation_sym, Hperm|apply list_elem_of_In, Hin].
Qed.

Lemma pairs_perm {A} (P : A → Prop) (f : A → A → result string bool) xs ys :
  (∀ x y, P x → P y → f x y = Ok true → f y x = Ok true) →
  Permutation xs ys → Forall P xs →
  BBM.for_all_pairs f xs = Ok true → BBM.for_all_pairs f ys = Ok true.
Proof.
  intros Hsym Hperm. induction Hperm as [|x xs ys Hperm IH|x y xs|xs ys zs Hxy IHxy Hyz IHyz];
    intros Hall Hok.
  - exact Hok.
  - apply Forall_cons_1 in Hall as [HP Hall].
    apply pairs_cons_true in Hok as [Hhead Htail]. apply pairs_cons_true. split.
    + eapply all_ok_perm; eassumption.
    + apply IH; assumption.
  - apply Forall_cons_1 in Hall as [HPy Hall]. apply Forall_cons_1 in Hall as [HPx Hall].
    apply pairs_cons_true in Hok as [Hy Htail]. apply all_ok_cons_true in Hy as [Hyx Hy].
    apply pairs_cons_true in Htail as [Hx Htail]. apply pairs_cons_true. split.
    + apply all_ok_cons_true. split; [apply Hsym; assumption|exact Hx].
    + apply pairs_cons_true. auto.
  - apply IHyz; [|apply IHxy; assumption]. apply Forall_forall. intros x Hin.
    apply (proj1 (Forall_forall P xs) Hall x). eapply Permutation_in;
      [apply Permutation_sym, Hxy|exact Hin].
Qed.

Definition offsets lvl (oa1 oa2 : prefix lvl) (addrs : list address) :=
  remove_dups (omap (λ addr,
    if decide (pa_prefix addr lvl = oa1 ∨ pa_prefix addr lvl = oa2)
    then Some (pa_offset lvl addr) else None) addrs).

Lemma offsets_sym lvl oa1 oa2 addrs : offsets lvl oa1 oa2 addrs = offsets lvl oa2 oa1 addrs.
Proof.
  unfold offsets. f_equal. apply list_omap_ext. induction addrs as [|addr addrs IH]; constructor; [|exact IH].
  repeat case_decide; naive_solver.
Qed.

Lemma mem_contents_eq_true_sym imem mem addrs time lvl oa1 oa2 :
  BBM.mem_contents_eq imem mem addrs time lvl oa1 oa2 = Ok true →
  BBM.mem_contents_eq imem mem addrs time lvl oa2 oa1 = Ok true.
Proof.
  unfold BBM.mem_contents_eq. fold (offsets lvl oa1 oa2 addrs) (offsets lvl oa2 oa1 addrs).
  change (all_ok (λ offs,
    byte1 ←@{result string} Memory.read_byte (pa_prefix_offset lvl oa1 offs) imem mem time;
    byte2 ← Memory.read_byte (pa_prefix_offset lvl oa2 offs) imem mem time;
    Ok (bool_decide (byte1 = byte2))) (offsets lvl oa1 oa2 addrs) = Ok true →
    all_ok (λ offs,
    byte2 ←@{result string} Memory.read_byte (pa_prefix_offset lvl oa2 offs) imem mem time;
    byte1 ← Memory.read_byte (pa_prefix_offset lvl oa1 offs) imem mem time;
    Ok (bool_decide (byte2 = byte1))) (offsets lvl oa2 oa1 addrs) = Ok true).
  rewrite (offsets_sym lvl oa2 oa1 addrs). intro Hrun. apply all_ok_true. intros offs Hin.
  pose proof (proj1 (all_ok_true _ _) Hrun offs Hin) as Hbytes.
  unfold mbind, result_bind, mret, result_ret in Hbytes |- *.
  destruct (Memory.read_byte (pa_prefix_offset lvl oa1 offs) imem mem time) as [byte1|err] eqn:Hfirst;
    destruct (Memory.read_byte (pa_prefix_offset lvl oa2 offs) imem mem time) as [byte2|err'] eqn:Hsecond;
    cbn in Hbytes |- *; try discriminate.
  injection Hbytes as Heq. apply bool_decide_eq_true in Heq. subst byte2.
  rewrite bool_decide_true by reflexivity. reflexivity.
Qed.

Lemma mem_contents_eq_btw_true_sym imem mem addrs tmin tmax lvl oa1 oa2 :
  BBM.mem_contents_eq_btw imem mem addrs tmin tmax lvl oa1 oa2 = Ok true →
  BBM.mem_contents_eq_btw imem mem addrs tmin tmax lvl oa2 oa1 = Ok true.
Proof.
  unfold BBM.mem_contents_eq_btw, mbind, result_bind, mret, result_ret.
  destruct (BBM.mem_contents_eq imem mem addrs tmin lvl oa1 oa2) as [b|err] eqn:Hread; [|discriminate].
  intro Hrun. injection Hrun as Hrun. apply andb_true_iff in Hrun as [-> Hunchanged].
  rewrite (mem_contents_eq_true_sym _ _ _ _ _ _ _ Hread). cbn. f_equal.
  apply bool_decide_eq_true in Hunchanged. apply bool_decide_eq_true.
  intros ev Hin. specialize (Hunchanged ev Hin). destruct (Ev.get_msg ev); tauto.
Qed.

Lemma violation_sym imem mem addrs bound ctxt e1 e2 events1 events2 :
  VMCacheOrder.ordered events1 → VMCacheOrder.ordered events2 →
  BBM.is_bbm_violation imem mem addrs bound ctxt e1 e2 events1 events2 = Ok false →
  BBM.is_bbm_violation imem mem addrs bound ctxt e2 e1 events2 events1 = Ok false.
Proof.
  intros Hfirst Hsecond. unfold BBM.is_bbm_violation.
  assert (Hintervals := time_intervals_sym bound events2 events1 Hsecond Hfirst).
  assert (Hoverlaps : BBM.time_overlaps bound events2 events1 = BBM.time_overlaps bound events1 events2).
  { unfold BBM.time_overlaps. rewrite Hintervals. reflexivity. }
  rewrite Hoverlaps, Hintervals.
  destruct (decide (is_final (TLB.Ctxt.lvl ctxt) (TLB.Entry.pte e1))) as [Hfinal1|Hfinal1];
    destruct (decide (is_final (TLB.Ctxt.lvl ctxt) (TLB.Entry.pte e2))) as [Hfinal2|Hfinal2].
  - assert (Heq : ∀ {A} `{EqDecision A} (a b : A), bool_decide (a = b) = bool_decide (b = a)).
    { intros. apply bool_decide_ext. intuition congruence. }
    rewrite (@Heq _ _ (attr_idx (TLB.Entry.pte e2)) (attr_idx (TLB.Entry.pte e1))),
      (@Heq _ _ (shareability (TLB.Entry.pte e2)) (shareability (TLB.Entry.pte e1))),
      (@Heq _ _ (is_contiguous (TLB.Entry.pte e2)) (is_contiguous (TLB.Entry.pte e1))).
    repeat match goal with |- context [if negb ?b then _ else _] => destruct b; cbn end; try tauto.
    repeat case_decide; try congruence; try tauto.
    destruct (BBM.time_intervals bound events1 events2) as [|interval intervals]; [tauto|].
    repeat case_decide; try congruence; cbn; try tauto.
    set (f := (λ '(tmin, tmax),
      BBM.mem_contents_eq_btw imem mem addrs tmin tmax (TLB.Ctxt.lvl ctxt)
        (output_prefix (TLB.Ctxt.lvl ctxt) (TLB.Entry.pte e1))
        (output_prefix (TLB.Ctxt.lvl ctxt) (TLB.Entry.pte e2))) : (nat * nat) → result string bool).
    set (g := (λ '(tmin, tmax),
      BBM.mem_contents_eq_btw imem mem addrs tmin tmax (TLB.Ctxt.lvl ctxt)
        (output_prefix (TLB.Ctxt.lvl ctxt) (TLB.Entry.pte e2))
        (output_prefix (TLB.Ctxt.lvl ctxt) (TLB.Entry.pte e1))) : (nat * nat) → result string bool).
    change (negb <$> all_ok f (interval :: intervals) = Ok false →
      negb <$> all_ok g (interval :: intervals) = Ok false).
    intro Hrun. apply negb_ok_true in Hrun. apply negb_ok_true, all_ok_true.
    intros [tmin tmax] Hin. apply mem_contents_eq_btw_true_sym.
    exact (proj1 (all_ok_true _ _) Hrun _ Hin).
  - rewrite bool_decide_true by exact Hfinal1. cbn. tauto.
  - rewrite bool_decide_true by exact Hfinal2. cbn. tauto.
  - rewrite !bool_decide_false by assumption. cbn. tauto.
Qed.

(** Uniqueness connects each stored row to its observable history. *)
Lemma lookup_assoc_value {K V} `{EqDecision K} (key : K) (value : V) rows :
  NoDup (map fst rows) → (lookup_assoc key rows = Some value ↔ (key, value) ∈ rows).
Proof.
  induction rows as [|[first val] rows IH]; intro Hunique; [split; [discriminate|inversion 1]|].
  cbn [map fst] in Hunique. apply list.NoDup_cons in Hunique as [Hfresh Hunique].
  cbn [lookup_assoc]. destruct (decide (key = first)) as [->|Hne].
  - split; [intro Heq; injection Heq as <-; left|]. intro Hin. apply elem_of_cons in Hin as [Heq|Hin].
    + injection Heq as ->. reflexivity.
    + exfalso. apply Hfresh. apply list_elem_of_fmap. exists (first, value). auto.
  - etrans; [apply IH, Hunique|]. split; [intro Hin; right; exact Hin|].
    intro Hin. apply elem_of_cons in Hin as [Heq|Hin]; [injection Heq as ->; contradiction|exact Hin].
Qed.

Lemma row_history cache ctxt entry events :
  VMCacheExchange.unique_entries cache →
  (entry, events) ∈ TLB.VATLB.get ctxt (TLB.vatlb cache) →
  VMCacheRefill.history cache (existT ctxt entry) = events.
Proof.
  intros Hunique Hin. unfold VMCacheRefill.history.
  change (default [] (lookup_assoc entry (TLB.VATLB.get ctxt (TLB.vatlb cache))) = events).
  rewrite (proj2 (lookup_assoc_value _ _ _ (Hunique ctxt)) Hin). reflexivity.
Qed.

Lemma nonempty_rows_equiv old new ctxt entry events :
  VMCacheExchange.unique_entries old → VMCacheExchange.unique_entries new →
  VMCacheRefill.equiv old new → events ≠ [] →
  ((entry, events) ∈ TLB.VATLB.get ctxt (TLB.vatlb old) ↔
   (entry, events) ∈ TLB.VATLB.get ctxt (TLB.vatlb new)).
Proof.
  intros Hold Hnew [_ Hhist] Hlive. split; intro Hin.
  - pose proof (row_history _ _ _ _ Hold Hin) as Hevents. rewrite Hhist in Hevents.
    unfold VMCacheRefill.history in Hevents.
    change (default [] (lookup_assoc entry (TLB.VATLB.get ctxt (TLB.vatlb new))) = events) in Hevents.
    apply (lookup_assoc_value _ _ _ (Hnew ctxt)).
    destruct (lookup_assoc entry (TLB.VATLB.get ctxt (TLB.vatlb new))); cbn in Hevents;
      [congruence|congruence].
  - pose proof (row_history _ _ _ _ Hnew Hin) as Hevents. rewrite <- Hhist in Hevents.
    unfold VMCacheRefill.history in Hevents.
    change (default [] (lookup_assoc entry (TLB.VATLB.get ctxt (TLB.vatlb old))) = events) in Hevents.
    apply (lookup_assoc_value _ _ _ (Hold ctxt)).
    destruct (lookup_assoc entry (TLB.VATLB.get ctxt (TLB.vatlb old))); cbn in Hevents;
      [congruence|congruence].
Qed.

Lemma rows_permutation old new ctxt :
  VMCacheExchange.unique_entries old → VMCacheExchange.unique_entries new →
  VMCacheRefill.equiv old new →
  Permutation (filter (λ row, row.2 ≠ []) (TLB.VATLB.get ctxt (TLB.vatlb old)))
    (filter (λ row, row.2 ≠ []) (TLB.VATLB.get ctxt (TLB.vatlb new))).
Proof.
  intros Hold Hnew Hequiv. apply list.NoDup_Permutation.
  - apply list.NoDup_filter. eapply NoDup_fmap_1. apply Hold.
  - apply list.NoDup_filter. eapply NoDup_fmap_1. apply Hnew.
  - intros [entry events]. split; intro Hin; apply list_elem_of_filter in Hin as [Hlive Hin];
      apply list_elem_of_filter; split; [exact Hlive| |exact Hlive|].
    + apply (nonempty_rows_equiv _ _ _ _ _ Hold Hnew Hequiv Hlive), Hin.
    + apply (nonempty_rows_equiv _ _ _ _ _ Hold Hnew Hequiv Hlive), Hin.
Qed.

Lemma foldl_or {A B} (step : B → A → B) (P : B → Prop) (Q : A → Prop) :
  (∀ acc x, P (step acc x) ↔ P acc ∨ Q x) →
  ∀ xs acc, P (foldl step acc xs) ↔ P acc ∨ ∃ x, x ∈ xs ∧ Q x.
Proof.
  intros Hstep xs. induction xs as [|x xs IH]; intro acc; cbn [foldl].
  - split; [auto|intros [H|[y [Hin _]]]; [exact H|inversion Hin]].
  - etrans; [apply IH|]. pose proof (Hstep acc x) as Hx. split.
    + intros [H|[y [Hin Hy]]].
      * apply Hx in H as [H|H]; [auto|right; exists x; split; [left|exact H]].
      * right. exists y. split; [right; exact Hin|exact Hy].
    + intros [H|[y [Hin Hy]]]; [left; apply Hx; auto|].
      apply elem_of_cons in Hin as [->|Hin]; [left; apply Hx; auto|right; exists y; auto].
Qed.

Lemma pairs_cache_equiv imem mem addrs bound ctxt old new :
  VMCacheExchange.unique_entries old → VMCacheExchange.unique_entries new →
  (∀ fe, VMCacheOrder.ordered (VMCacheRefill.history old fe)) →
  VMCacheRefill.equiv old new →
  BBM.for_all_pairs (λ '(e1, h1) '(e2, h2),
    negb <$> BBM.is_bbm_violation imem mem addrs bound ctxt e1 e2 h1 h2)
    (TLB.VATLB.get ctxt (TLB.vatlb old)) = Ok true →
  BBM.for_all_pairs (λ '(e1, h1) '(e2, h2),
    negb <$> BBM.is_bbm_violation imem mem addrs bound ctxt e1 e2 h1 h2)
    (TLB.VATLB.get ctxt (TLB.vatlb new)) = Ok true.
Proof.
  intros Hold Hnew Hordered Hequiv Hrun.
  rewrite <- VMBBMReplay.pair_check_nonempty in Hrun |- *.
  eapply (pairs_perm (λ row, VMCacheOrder.ordered row.2)); [| | |exact Hrun].
  - intros [e1 h1] [e2 h2] H1 H2 Hxy. apply negb_ok_false. apply negb_ok_false in Hxy.
    eapply violation_sym; eassumption.
  - apply rows_permutation; assumption.
  - apply Forall_forall. intros [entry events] Hin. apply list_elem_of_In, list_elem_of_filter in Hin as [_ Hin].
    rewrite <- (row_history old ctxt entry events Hold Hin). apply Hordered.
Qed.

Definition ctxt_rows := { ctxt : TLB.Ctxt.t & list (TLB.Entry.t (TLB.Ctxt.lvl ctxt) * TLB.Entry.events) }.

Lemma ebc_level_member (vatlb : TLB.VATLB.t) lvl (acc : list ctxt_rows) (row : ctxt_rows) :
  row ∈ map_fold (λ nd (entries : list (TLB.Entry.t lvl * TLB.Entry.events)) (acc : list ctxt_rows),
      existT (existT lvl nd : TLB.Ctxt.t) entries :: acc)
    acc (hget lvl vatlb) ↔
  row ∈ acc ∨ ∃ (nd : TLB.NDCtxt.t lvl) (entries : list (TLB.Entry.t lvl * TLB.Entry.events)),
    hget lvl vatlb !! nd = Some entries ∧
    row = existT (existT lvl nd : TLB.Ctxt.t) entries.
Proof.
  rewrite (map_fold_foldr (M := gmap (TLB.NDCtxt.t lvl))).
  assert (Hrows : ∀ rows, row ∈ foldr
    (uncurry (λ nd (entries : list (TLB.Entry.t lvl * TLB.Entry.events)) (acc : list ctxt_rows),
      existT (existT lvl nd : TLB.Ctxt.t) entries :: acc)) acc rows ↔
    row ∈ acc ∨ ∃ (nd : TLB.NDCtxt.t lvl) (entries : list (TLB.Entry.t lvl * TLB.Entry.events)),
      (nd, entries) ∈ rows ∧ row = existT (existT lvl nd : TLB.Ctxt.t) entries).
  { intro rows. induction rows as [|[nd entries] rows IH]; cbn [foldr uncurry].
    - split; [auto|intros [H|[? [? [Hin _]]]]; [exact H|inversion Hin]].
    - etrans; [apply elem_of_cons|]. split.
      + intros [Heq|Hin]; [right; exists nd, entries; split; [left|exact Heq]|].
        apply IH in Hin as [Hin|[nd' [entries' [Hin Heq]]]]; [auto|].
        right. exists nd', entries'. split; [right; exact Hin|exact Heq].
      + intros [Hin|[nd' [entries' [Hin Heq]]]]; [right; apply IH; auto|].
        apply elem_of_cons in Hin as [Heq'|Hin].
        * injection Heq' as -> ->. left. exact Heq.
        * right. apply IH. right. exists nd', entries'. auto. }
  etrans; [apply Hrows|]. split; intros [Hin|[nd [entries [Hin Heq]]]]; [auto| |auto|].
  - right. exists nd, entries. split; [|exact Heq].
    apply (elem_of_map_to_list (M := gmap (TLB.NDCtxt.t lvl))), Hin.
  - right. exists nd, entries. split; [|exact Heq].
    apply (elem_of_map_to_list (M := gmap (TLB.NDCtxt.t lvl))), Hin.
Qed.

Lemma ebc_member vatlb ctxt entries :
  existT ctxt entries ∈ TLB.VATLB.entries_by_ctxt vatlb ↔
  hget (TLB.Ctxt.lvl ctxt) vatlb !! TLB.Ctxt.nd ctxt = Some entries.
Proof.
  unfold TLB.VATLB.entries_by_ctxt.
  etrans; [apply (foldl_or _ (λ rows, existT ctxt entries ∈ rows)
    (λ lvl, ∃ (nd : TLB.NDCtxt.t lvl) (es : list (TLB.Entry.t lvl * TLB.Entry.events)),
      hget lvl vatlb !! nd = Some es ∧
      existT ctxt entries = existT (existT lvl nd : TLB.Ctxt.t) es)); intros acc lvl; apply ebc_level_member|].
  split.
  - intros [Hin|[lvl [_ [nd [es [Hlookup Heq]]]]]]; [inversion Hin|].
    pose proof (f_equal projT1 Heq) as Hctxt. cbn in Hctxt. subst ctxt.
    apply (inj (existT (existT lvl nd))) in Heq. subst es. exact Hlookup.
  - intro Hlookup. right. destruct ctxt as [lvl nd]. exists lvl. split; [apply elem_of_enum|].
    exists nd, entries. auto.
Qed.

Lemma ebc_get vatlb ctxt entries :
  existT ctxt entries ∈ TLB.VATLB.entries_by_ctxt vatlb → TLB.VATLB.get ctxt vatlb = entries.
Proof. intro Hin. apply ebc_member in Hin. unfold TLB.VATLB.get. rewrite Hin. reflexivity. Qed.

Lemma ebc_get_nonempty vatlb ctxt :
  TLB.VATLB.get ctxt vatlb ≠ [] →
  existT ctxt (TLB.VATLB.get ctxt vatlb) ∈ TLB.VATLB.entries_by_ctxt vatlb.
Proof.
  intro Hlive. apply ebc_member. unfold TLB.VATLB.get in *.
  destruct (hget (TLB.Ctxt.lvl ctxt) vatlb !! TLB.Ctxt.nd ctxt); [reflexivity|contradiction].
Qed.

(** Descendant membership records the source row and its parent relation;
    neither the fold order nor empty context buckets affect this relation. *)
Definition gd_prepend (ctxt : TLB.Ctxt.t) (fes : list (TLB.FE.t * TLB.Entry.events)) (gd : BBM.gdesc) :=
  hset (TLB.Ctxt.lvl ctxt)
    (partial_alter (λ x, Some ((fes ++ default [] x)%list)) (TLB.Ctxt.nd ctxt)
      (hget (TLB.Ctxt.lvl ctxt) gd)) gd.

Lemma gd_prepend_member query parent fes gd x :
  x ∈ BBM.gdesc_get query (gd_prepend parent fes gd) ↔
    x ∈ BBM.gdesc_get query gd ∨ query = parent ∧ x ∈ fes.
Proof.
  destruct query as [qlvl qnd], parent as [plvl pnd].
  unfold gd_prepend, BBM.gdesc_get. cbn [TLB.Ctxt.lvl TLB.Ctxt.nd projT1 projT2].
  destruct (decide (qlvl = plvl)) as [->|Hlevel].
  - rewrite hvec_get_set_same.
    destruct (decide (qnd = pnd)) as [->|Hnd].
    + rewrite (lookup_partial_alter_eq (M := gmap (TLB.NDCtxt.t plvl))).
      cbn [default]. etrans; [apply elem_of_app|]. tauto.
    + rewrite (lookup_partial_alter_ne (M := gmap (TLB.NDCtxt.t plvl))) by congruence.
      assert ((existT plvl qnd : TLB.Ctxt.t) ≠ existT plvl pnd).
      { intro Heq. apply (inj (existT plvl)) in Heq. contradiction. }
      tauto.
  - rewrite hvec_get_set_diff by exact Hlevel.
    assert ((existT qlvl qnd : TLB.Ctxt.t) ≠ existT plvl pnd).
    { intro Heq. apply (f_equal projT1) in Heq. cbn in Heq. contradiction. }
    tauto.
Qed.

Definition gd_levels (ctxt : TLB.Ctxt.t) (fes : list (TLB.FE.t * TLB.Entry.events))
    (gd : BBM.gdesc) (levels : list Level) :=
  foldl (λ gd (plvl : Level), if decide (plvl < TLB.Ctxt.lvl ctxt)
    then gd_prepend (BBM.ctxt_parent ctxt plvl None) fes gd else gd) gd levels.

Lemma gd_levels_member query ctxt fes gd levels x :
  x ∈ BBM.gdesc_get query (gd_levels ctxt fes gd levels) ↔
    x ∈ BBM.gdesc_get query gd ∨
    ∃ plvl : Level, plvl ∈ levels ∧ plvl < TLB.Ctxt.lvl ctxt ∧
      query = BBM.ctxt_parent ctxt plvl None ∧ x ∈ fes.
Proof.
  unfold gd_levels. apply (foldl_or _ (λ gd, x ∈ BBM.gdesc_get query gd)
    (λ plvl : Level, plvl < TLB.Ctxt.lvl ctxt ∧ query = BBM.ctxt_parent ctxt plvl None ∧ x ∈ fes)).
  intros acc plvl. destruct (decide (plvl < TLB.Ctxt.lvl ctxt)) as [Hlt|Hlt].
  - etrans; [apply gd_prepend_member|]. tauto.
  - tauto.
Qed.

Definition descendant (query source : TLB.Ctxt.t) :=
  TLB.Ctxt.asid source = None ∧ TLB.Ctxt.lvl query < TLB.Ctxt.lvl source ∧
  query = BBM.ctxt_parent source (TLB.Ctxt.lvl query) None.

Definition gd_row (gd : BBM.gdesc) (row : ctxt_rows) :=
  let '(existT ctxt entries) := row in
  if TLB.Ctxt.asid ctxt is Some _ then gd else
    gd_levels ctxt (map (λ '(entry, events), (existT ctxt entry : TLB.FE.t, events)) entries)
      gd (enum Level).

Lemma gd_row_member query gd row x :
  x ∈ BBM.gdesc_get query (gd_row gd row) ↔
    x ∈ BBM.gdesc_get query gd ∨
    let '(existT ctxt entries) := row in
    descendant query ctxt ∧ x ∈ map (λ '(entry, events), (existT ctxt entry : TLB.FE.t, events)) entries.
Proof.
  destruct row as [ctxt entries]. unfold gd_row, descendant.
  destruct (TLB.Ctxt.asid ctxt) as [asid|] eqn:Hasid; [intuition discriminate|].
  etrans; [apply gd_levels_member|]. split.
  - intros [Hin|[plvl [_ [Hlt [Heq Hin]]]]]; [auto|right].
    pose proof (f_equal TLB.Ctxt.lvl Heq) as Hlevel. cbn in Hlevel. subst plvl. auto.
  - intros [Hin|[[_ [Hlt Heq]] Hin]]; [auto|right].
    exists (TLB.Ctxt.lvl query). split; [apply elem_of_enum|auto].
Qed.

Lemma gdesc_member ebc query fe events :
  (fe, events) ∈ BBM.gdesc_get query (BBM.global_descendants ebc) ↔
  ∃ ctxt entries entry, existT ctxt entries ∈ ebc ∧ (entry, events) ∈ entries ∧
    fe = existT ctxt entry ∧ descendant query ctxt.
Proof.
  change (BBM.global_descendants ebc) with (foldl gd_row (hvec_func (λ _, ∅)) ebc).
  etrans; [apply (foldl_or _ (λ gd, (fe, events) ∈ BBM.gdesc_get query gd)
    (λ row, let '(existT ctxt entries) := row in descendant query ctxt ∧
      (fe, events) ∈ map (λ '(entry, events), (existT ctxt entry : TLB.FE.t, events)) entries));
      intros acc row; apply gd_row_member|].
  assert (Hempty : BBM.gdesc_get query (hvec_func (λ _, ∅)) = []).
  { unfold BBM.gdesc_get. rewrite hvec_get_func,
      (lookup_empty (M := gmap (TLB.NDCtxt.t (TLB.Ctxt.lvl query)))). reflexivity. }
  rewrite Hempty. split.
  - intros [Hin|[[ctxt entries] [Hin [Hdesc Hrow]]]]; [inversion Hin|].
    apply list_elem_of_fmap in Hrow as [[entry evs] [Heq Hrow]].
    injection Heq as Hfe Hevents. subst fe evs. exists ctxt, entries, entry. auto.
  - intros [ctxt [entries [entry [Hin [Hrow [-> Hdesc]]]]]].
    right. exists (existT ctxt entries). split; [exact Hin|]. split; [exact Hdesc|].
    apply list_elem_of_fmap. exists (entry, events). auto.
Qed.

Lemma gdesc_nonempty_transfer old new query fe events :
  VMCacheExchange.unique_entries old → VMCacheExchange.unique_entries new →
  VMCacheRefill.equiv old new → events ≠ [] →
  (fe, events) ∈ BBM.gdesc_get query (BBM.global_descendants (TLB.VATLB.entries_by_ctxt (TLB.vatlb old))) →
  (fe, events) ∈ BBM.gdesc_get query (BBM.global_descendants (TLB.VATLB.entries_by_ctxt (TLB.vatlb new))).
Proof.
  intros Hold Hnew Hequiv Hlive Hin. apply gdesc_member in Hin as [ctxt [entries [entry [Hctxt [Hrow [-> Hdesc]]]]]].
  rewrite <- (ebc_get _ _ _ Hctxt) in Hrow.
  apply (nonempty_rows_equiv _ _ _ _ _ Hold Hnew Hequiv Hlive) in Hrow.
  apply gdesc_member. exists ctxt, (TLB.VATLB.get ctxt (TLB.vatlb new)), entry.
  split; [|auto]. apply ebc_get_nonempty. intro Hnil. rewrite Hnil in Hrow. inversion Hrow.
Qed.

Lemma overlap_nonempty bound events other : BBM.time_overlaps bound events other = true →
  events ≠ [] ∧ other ≠ [].
Proof.
  intro Hoverlap. split; intro Hnil; subst;
    rewrite ?VMBBMReplay.time_overlaps_nil_l, ?VMBBMReplay.time_overlaps_nil_r in Hoverlap; discriminate.
Qed.

Definition conflicts (vatlb : TLB.VATLB.t) bound (ctxt : TLB.Ctxt.t)
    (entries : list (TLB.Entry.t (TLB.Ctxt.lvl ctxt) * TLB.Entry.events)) : Prop :=
  ∃ '(e, events) ∈ entries, is_final (TLB.Ctxt.lvl ctxt) (TLB.Entry.pte e) ∧
    ((∃ plvl : Level, plvl < TLB.Ctxt.lvl ctxt ∧
      ∃ '(pe, pevs) ∈ TLB.VATLB.get (BBM.ctxt_parent ctxt plvl (TLB.Ctxt.asid ctxt)) vatlb,
        is_final plvl (TLB.Entry.pte pe) ∧ BBM.time_overlaps bound events pevs = true) ∨
     (is_Some (TLB.Ctxt.asid ctxt) ∧ ∃ glvl : Level, glvl ≤ TLB.Ctxt.lvl ctxt ∧
      ∃ '(ge, gevs) ∈ TLB.VATLB.get (BBM.ctxt_parent ctxt glvl None) vatlb,
        BBM.time_overlaps bound events gevs = true) ∨
     (is_Some (TLB.Ctxt.asid ctxt) ∧
      ∃ '(ge, gevs) ∈ BBM.gdesc_get (BBM.ctxt_parent ctxt (TLB.Ctxt.lvl ctxt) None)
        (BBM.global_descendants (TLB.VATLB.entries_by_ctxt vatlb)),
        BBM.time_overlaps bound events gevs = true)).
#[local] Typeclasses Transparent conflicts.

Lemma pair_list_exists_dec {A B} (P : A → B → Prop) (rows : list (A * B)) :
  (∀ a b, Decision (P a b)) → Decision (∃ '(a, b) ∈ rows, P a b).
Proof.
  intro Hdec.
  destruct (list_exist_dec (λ row : A * B, P row.1 row.2) rows (λ row, Hdec row.1 row.2)) as [Hyes|Hno].
  - left. destruct Hyes as [[a b] [Hin HP]]. exists (a, b). auto.
  - right. intros [[a b] [Hin HP]]. apply Hno. exists (a, b). auto.
Defined.

#[local] Instance conflicts_dec vatlb bound ctxt entries : Decision (conflicts vatlb bound ctxt entries).
Proof.
  unfold conflicts. apply pair_list_exists_dec. intros entry events.
  apply and_dec; [apply _|]. apply or_dec.
  - apply exists_dec. intro plvl. apply and_dec; [apply _|].
    apply pair_list_exists_dec. intros entry' events'. apply and_dec; apply _.
  - apply or_dec.
    + apply and_dec; [apply _|]. apply exists_dec. intro glvl. apply and_dec; [apply _|].
      apply pair_list_exists_dec. intros entry' events'. apply _.
    + apply and_dec; [apply _|]. apply pair_list_exists_dec. intros entry' events'. apply _.
Defined.

Lemma conflicts_transfer old new bound ctxt :
  VMCacheExchange.unique_entries old → VMCacheExchange.unique_entries new →
  VMCacheRefill.equiv old new →
  conflicts (TLB.vatlb old) bound ctxt (TLB.VATLB.get ctxt (TLB.vatlb old)) →
  conflicts (TLB.vatlb new) bound ctxt (TLB.VATLB.get ctxt (TLB.vatlb new)).
Proof.
  intros Hold Hnew Hequiv [ [entry events] [Hrow [Hfinal Hconflict]] ].
  assert (Hlive : events ≠ []).
  { destruct Hconflict as [[plvl [_ [[pe pevs] [_ [_ Hoverlap]]]]]|[[_ [glvl [_ [[ge gevs] [_ Hoverlap]]]]]|[_ [[ge gevs] [_ Hoverlap]]]]];
      exact (proj1 (overlap_nonempty _ _ _ Hoverlap)). }
  exists (entry, events). split.
  - apply (nonempty_rows_equiv _ _ _ _ _ Hold Hnew Hequiv Hlive), Hrow.
  - split; [exact Hfinal|].
    destruct Hconflict as [[plvl [Hlt [[pe pevs] [Hin [Hpe Hoverlap]]]]]|[[Hasid [glvl [Hle [[ge gevs] [Hin Hoverlap]]]]]|[Hasid [[ge gevs] [Hin Hoverlap]]]]].
    + left. exists plvl. split; [exact Hlt|]. exists (pe, pevs). split; [|auto].
      apply (nonempty_rows_equiv _ _ _ _ _ Hold Hnew Hequiv (proj2 (overlap_nonempty _ _ _ Hoverlap))), Hin.
    + right; left. split; [exact Hasid|]. exists glvl. split; [exact Hle|]. exists (ge, gevs). split; [|exact Hoverlap].
      apply (nonempty_rows_equiv _ _ _ _ _ Hold Hnew Hequiv (proj2 (overlap_nonempty _ _ _ Hoverlap))), Hin.
    + right; right. split; [exact Hasid|]. exists (ge, gevs). split; [|exact Hoverlap].
      eapply gdesc_nonempty_transfer; [exact Hold|exact Hnew|exact Hequiv| |exact Hin].
      exact (proj2 (overlap_nonempty _ _ _ Hoverlap)).
Qed.

Definition pair_check imem mem addrs bound ctxt entries :=
  BBM.for_all_pairs (λ '(e1, h1) '(e2, h2),
    negb <$> BBM.is_bbm_violation imem mem addrs bound ctxt e1 e2 h1 h2) entries.

Definition context_check imem mem addrs vatlb bound ctxt entries : result string bool :=
  if entries is [] then Ok false else
  no_pair_violation ← pair_check imem mem addrs bound ctxt entries;
  Ok (negb no_pair_violation || bool_decide (conflicts vatlb bound ctxt entries)).

Lemma context_check_false imem mem addrs vatlb bound ctxt entries :
  context_check imem mem addrs vatlb bound ctxt entries = Ok false ↔
  pair_check imem mem addrs bound ctxt entries = Ok true ∧ ¬ conflicts vatlb bound ctxt entries.
Proof.
  destruct entries as [|entry entries].
  - split; [intros _; split; [reflexivity|intros [[entry events] [Hin _]]; inversion Hin]|intros _; reflexivity].
  - unfold context_check, mbind, result_bind.
    destruct (pair_check imem mem addrs bound ctxt (entry :: entries)) as [[]|err];
      try case_bool_decide; cbn; intuition congruence.
Qed.

Definition any_ok {A} (f : A → result string bool) xs := List.existsb id <$> mapM f xs.

Lemma any_ok_cons {A} (f : A → result string bool) x xs :
  any_ok f (x :: xs) = (b ← f x; rest ← any_ok f xs; mret (b || rest)).
Proof.
  unfold any_ok. cbn [mapM]. unfold mbind, result_bind, fmap, result_fmap, mret, result_ret.
  destruct (f x); [destruct (mapM f xs); reflexivity|reflexivity].
Qed.

Lemma any_ok_cons_false {A} (f : A → result string bool) x xs :
  any_ok f (x :: xs) = Ok false ↔ f x = Ok false ∧ any_ok f xs = Ok false.
Proof.
  rewrite any_ok_cons. unfold mbind, result_bind, mret, result_ret.
  destruct (f x) as [[]|err], (any_ok f xs) as [[]|err']; cbn; intuition congruence.
Qed.

Lemma any_ok_false {A} (f : A → result string bool) xs :
  any_ok f xs = Ok false ↔ ∀ x, x ∈ xs → f x = Ok false.
Proof.
  induction xs as [|x xs IH].
  - split; [intros _ y Hin; inversion Hin|intros _; reflexivity].
  - etrans; [apply any_ok_cons_false|]. split.
    + intros [Hx Hxs] y Hin. apply elem_of_cons in Hin as [->|Hin]; [exact Hx|exact (proj1 IH Hxs y Hin)].
    + intro H. split; [apply H; left|apply IH; intros y Hin; apply H; right; exact Hin].
Qed.

Lemma check_tlb_shape imem mem addrs cache :
  BBM.check_tlb imem mem addrs cache =
  any_ok (λ '(existT ctxt entries),
    context_check imem mem addrs (TLB.vatlb cache) (length mem) ctxt entries)
    (TLB.VATLB.entries_by_ctxt (TLB.vatlb cache)).
Proof.
  unfold BBM.check_tlb, any_ok. apply f_equal.
  match goal with |- mapM ?f ?xs = mapM ?g ?xs =>
    assert (Hfunctions : f = g); [|rewrite Hfunctions; reflexivity]
  end.
  apply functional_extensionality. intros [ctxt entries]. cbn beta iota zeta.
  destruct entries as [|entry entries]; [reflexivity|].
  unfold context_check, pair_check.
  match goal with |- context [BBM.for_all_pairs ?f ?xs] =>
    destruct (BBM.for_all_pairs f xs) as [no_pair|err]
  end; cbn [mbind result_bind]; [|reflexivity].
  apply (f_equal (@Ok string bool)). apply (f_equal (orb (negb no_pair))).
  apply bool_decide_ext. reflexivity.
Qed.

Lemma check_tlb_false imem mem addrs cache :
  BBM.check_tlb imem mem addrs cache = Ok false ↔
  ∀ ctxt, pair_check imem mem addrs (length mem) ctxt (TLB.VATLB.get ctxt (TLB.vatlb cache)) = Ok true ∧
    ¬ conflicts (TLB.vatlb cache) (length mem) ctxt (TLB.VATLB.get ctxt (TLB.vatlb cache)).
Proof.
  rewrite check_tlb_shape.
  split.
  - intros Hrun ctxt. apply context_check_false.
    destruct (decide (TLB.VATLB.get ctxt (TLB.vatlb cache) = [])) as [Hnil|Hlive];
      [rewrite Hnil; reflexivity|].
    apply (proj1 (any_ok_false _ _) Hrun (existT ctxt (TLB.VATLB.get ctxt (TLB.vatlb cache)))).
    apply ebc_get_nonempty, Hlive.
  - intro H. apply any_ok_false. intros [ctxt entries] Hin.
    rewrite <- (ebc_get _ _ _ Hin). apply context_check_false, H.
Qed.

(** Successful final validation depends only on histories. Error text can
    depend on the order in which entries are checked. *)
Theorem check_tlb_equiv imem mem addrs old new :
  VMCacheExchange.unique_entries old → VMCacheExchange.unique_entries new →
  (∀ fe, VMCacheOrder.ordered (VMCacheRefill.history old fe)) →
  (∀ fe, VMCacheOrder.ordered (VMCacheRefill.history new fe)) →
  VMCacheRefill.equiv old new →
  BBM.check_tlb imem mem addrs old = Ok false →
  BBM.check_tlb imem mem addrs new = Ok false.
Proof.
  intros Hold Hnew Hordered Hordered' Hequiv Hrun. apply check_tlb_false. intro ctxt.
  destruct (proj1 (check_tlb_false _ _ _ _) Hrun ctxt) as [Hpairs Hconflicts]. split.
  - exact (pairs_cache_equiv imem mem addrs (length mem) ctxt old new Hold Hnew Hordered Hequiv Hpairs).
  - intro Hbad. apply Hconflicts. eapply conflicts_transfer;
      [exact Hnew|exact Hold|apply VMCacheRefill.equiv_sym, Hequiv|exact Hbad].
Qed.

Corollary check_tlb_good_equiv imem mem addrs old new old_bound new_bound :
  VMCacheExchange.unique_entries old → VMCacheExchange.unique_entries new →
  VMCacheOrder.good old_bound old → VMCacheOrder.good new_bound new →
  VMCacheRefill.equiv old new →
  BBM.check_tlb imem mem addrs old = Ok false →
  BBM.check_tlb imem mem addrs new = Ok false.
Proof.
  intros Hold Hnew Hgood Hgood' Hequiv Hrun. eapply check_tlb_equiv;
    [exact Hold|exact Hnew|intro fe; exact (proj1 (Hgood fe))|
     intro fe; exact (proj1 (Hgood' fe))|exact Hequiv|exact Hrun].
Qed.

End VMBBMTransport.
