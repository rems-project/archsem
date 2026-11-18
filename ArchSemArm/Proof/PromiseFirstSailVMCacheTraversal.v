(******************************************************************************)
(* Ordered batches underlying the actual table traversal                     *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheRefill PromiseFirstSailVMCacheConfig.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMCacheTraversal.
Import VMPromising VMCacheRefill.
Local Notation action A := (stateT TLB.t (result string) A).

Lemma last_append_cast {A n} (values : vec A n) value m (cast : n + 1 = S m) :
  Vector.last (ctrans cast (values +++ [#value])) = value.
Proof.
  revert m cast. induction values as [|head n values IH]; intros m cast.
  - assert (m = 0) by (cbn in cast; lia). subst m. reflexivity.
  - destruct m as [|m]; [cbn in cast; lia|].
    cbn [vapp Vector.append]. rewrite ctrans_vec_vcons. cbn [Vector.last]. apply IH.
Qed.

Lemma append_pte entry idx pte child :
  TLB.FE.append entry idx pte = Ok child → TLB.FE.pte child = pte.
Proof.
  unfold TLB.FE.append. destruct (inspect (child_lvl (TLB.FE.lvl entry))) as [[lvl|] Hlvl];
    [|discriminate]. intro Happend. injection Happend as <-.
  unfold TLB.FE.pte, TLB.FE.entry, TLB.Entry.pte, TLB.Entry.append. cbn.
  apply (last_append_cast (TLB.Entry.ptes (TLB.FE.entry entry)) pte lvl).
Qed.

Lemma append_level entry idx pte child lvl :
  child_lvl (TLB.FE.lvl entry) = Some lvl → TLB.FE.append entry idx pte = Ok child →
  TLB.FE.lvl child = lvl.
Proof.
  intro Hlvl. unfold TLB.FE.append.
  destruct (inspect (child_lvl (TLB.FE.lvl entry))) as [[level|] Hlevel]; [|discriminate].
  assert (level = lvl) by congruence. subst level. intro Happend. injection Happend as <-. reflexivity.
Qed.

Lemma append_table entry idx pte child lvl :
  child_lvl (TLB.FE.lvl entry) = Some lvl → TLB.FE.append entry idx pte = Ok child →
  (TLB.FE.is_table child ↔ is_table lvl pte).
Proof.
  intros Hlvl Happend. unfold TLB.FE.is_table, TLB.Entry.is_table.
  change (is_table (TLB.FE.lvl child) (TLB.FE.pte child) ↔ is_table lvl pte).
  rewrite (append_level entry idx pte child lvl Hlvl Happend), (append_pte entry idx pte child Happend).
  reflexivity.
Qed.

Lemma fill_batch_app time keep first second cache :
  fill_batch time keep (first ++ second)%list cache =
    (left ← fill_batch time keep first; right ← fill_batch time keep second;
      mret (left ++ right)%list) cache.
Proof.
  revert cache. induction first as [|entry first IH]; intro cache.
  - change (fill_batch time keep second cache =
      (fill_batch time keep second cache ≫= λ '(next, outputs), Ok (next, outputs))).
    destruct (fill_batch time keep second cache) as [[next outputs]|err]; reflexivity.
  - cbn [app fill_batch]. unfold mbind, st_bind, result_bind.
  destruct (TLB.fill_entry time entry cache) as [[mid loaded]|err]; [|reflexivity]. cbn.
  rewrite IH. unfold mbind, st_bind, result_bind.
  destruct (fill_batch time keep first mid) as [[next outputs]|err]; cbn; [|reflexivity].
  destruct (fill_batch time keep second next) as [[last outputs']|err]; cbn; [|reflexivity].
  cbn. rewrite app_assoc. reflexivity.
Qed.

Lemma expand_batches {A} time keep (expand : A → result string (list TLB.FE.t)) entries cache :
  (List.concat <$> mapM (λ entry, targets ← mlift (expand entry);
      fill_batch time keep targets) entries) cache =
  (targets ← mapM expand entries; fill_batch time keep (List.concat targets) cache).
Proof.
  set (run := λ entry, targets ← mlift (expand entry); fill_batch time keep targets).
  change ((List.concat <$> mapM run entries) cache =
    (targets ← mapM expand entries; fill_batch time keep (List.concat targets) cache)).
  revert cache. induction entries as [|entry entries IH]; intro cache; [reflexivity|].
  assert (Hhead : run entry cache =
    (targets ← expand entry; fill_batch time keep targets cache)).
  { unfold run, mlift, st_lift, mbind, st_bind, result_bind, fmap, result_fmap.
    destruct (expand entry); reflexivity. }
  cbn [mapM]. unfold fmap, st_fmap, result_fmap, mbind, st_bind, result_bind.
  rewrite Hhead.
  destruct (expand entry) as [targets|err] eqn:Hexpand; [|reflexivity]. cbn.
  destruct (fill_batch_total time keep targets cache) as [mid [outputs Hbatch]].
  rewrite Hbatch. cbn.
  pose proof (IH mid) as Htail.
  destruct (mapM expand entries) as [target_lists|err] eqn:Htargets.
  - cbn in Htail |- *. rewrite fill_batch_app. unfold mbind, st_bind, result_bind. rewrite Hbatch. cbn.
    rewrite <- Htail. unfold fmap, st_fmap, result_fmap.
    destruct (mapM run entries mid) as [[last outputs']|err]; reflexivity.
  - cbn in Htail |- *. unfold fmap, st_fmap, result_fmap in Htail |- *.
    destruct (mapM run entries mid) as [[last outputs']|err']; [discriminate|]. exact Htail.
Qed.

Definition keep_table fe := bool_decide (TLB.FE.is_table fe).

Definition child_targets imem mem time entry lvl idx : result string (list TLB.FE.t) :=
  match Memory.read_word (index_table (TLB.FE.next_table entry) idx) imem mem time with
  | Ok pte => if decide (is_tlb_fillable lvl pte)
      then child ← TLB.FE.append entry idx pte; mret [child]
      else mret []
  | Error _ => mret []
  end.

Definition fill_child imem mem time entry lvl idx : action (list TLB.FE.t) :=
  match Memory.read_word (index_table (TLB.FE.next_table entry) idx) imem mem time with
  | Ok pte => if decide (is_tlb_fillable lvl pte) then
      child ← mlift (TLB.FE.append entry idx pte);
      loaded ← TLB.fill_entry time child;
      if (loaded : bool) then if decide (is_table lvl pte) then mret [child] else mret [] else mret []
    else mret []
  | Error _ => mret []
  end.

Lemma fill_child_batch imem mem time entry lvl idx cache :
  child_lvl (TLB.FE.lvl entry) = Some lvl →
  fill_child imem mem time entry lvl idx cache =
    (targets ← child_targets imem mem time entry lvl idx; fill_batch time keep_table targets cache).
Proof.
  intro Hlvl. unfold fill_child, child_targets.
  destruct (Memory.read_word _ imem mem time) as [pte|err]; [|reflexivity].
  destruct (decide (is_tlb_fillable lvl pte)); [|reflexivity].
  unfold mbind, st_bind, result_bind, mlift, st_lift, fmap, result_fmap.
  destruct (TLB.FE.append entry idx pte) as [child|err] eqn:Happend; [|reflexivity]. cbn.
  cbn [fill_batch]. unfold mbind, st_bind, result_bind.
  destruct (TLB.fill_entry time child cache) as [[next loaded]|err]; [|reflexivity].
  destruct loaded; [|reflexivity].
  unfold emitted, keep_table. cbn [andb].
  pose proof (append_table entry idx pte child lvl Hlvl Happend) as Htable.
  destruct (decide (is_table lvl pte)) as [Hyes|Hno].
  - rewrite bool_decide_true by (apply Htable; exact Hyes). reflexivity.
  - rewrite bool_decide_false by (intro Hyes; apply Hno, Htable, Hyes). reflexivity.
Qed.

Definition entry_targets imem mem time (present : gmap pn (list (bv 9))) entry : result string (list TLB.FE.t) :=
  guard_or "Fill_from_entry should only take tables" (TLB.FE.is_table entry);;
  lvl ← othrow "Filling from level 3 entry" (child_lvl (TLB.FE.lvl entry));
  List.concat <$> mapM (child_targets imem mem time entry lvl) (present !!! TLB.FE.next_table entry).

Theorem fill_from_entry_batch imem mem time entry cache :
  TLB.fill_from_entry imem mem time entry cache =
    (targets ← entry_targets imem mem time (TLB.pte_present cache) entry;
      fill_batch time keep_table targets cache).
Proof.
  unfold TLB.fill_from_entry, entry_targets, guard_or.
  destruct (decide (TLB.FE.is_table entry)); [|reflexivity].
  destruct (child_lvl (TLB.FE.lvl entry)) as [lvl|] eqn:Hlvl; [|reflexivity].
  change ((List.concat <$> mapM (fill_child imem mem time entry lvl)
    (TLB.pte_present cache !!! TLB.FE.next_table entry)) cache =
    (targets ← List.concat <$> mapM (child_targets imem mem time entry lvl)
      (TLB.pte_present cache !!! TLB.FE.next_table entry); fill_batch time keep_table targets cache)).
  assert (Hchild : fill_child imem mem time entry lvl =
    λ idx, targets ← mlift (child_targets imem mem time entry lvl idx); fill_batch time keep_table targets).
  { extensionality idx. extensionality state. rewrite fill_child_batch by exact Hlvl.
    unfold mlift, st_lift, mbind, st_bind, result_bind, fmap, result_fmap.
    destruct (child_targets imem mem time entry lvl idx); reflexivity. }
  rewrite Hchild, expand_batches.
  unfold fmap, result_fmap, mbind, result_bind.
  destruct (mapM (child_targets imem mem time entry lvl)
    (TLB.pte_present cache !!! TLB.FE.next_table entry)); reflexivity.
Qed.


Lemma fill_batch_config time keep entries : VMCacheConfig.preserves (fill_batch time keep entries).
Proof.
  induction entries as [|entry rest IH]; cbn [fill_batch]; [apply VMCacheConfig.preserves_ret|].
  apply VMCacheConfig.preserves_bind; [apply VMCacheConfig.fill_entry|]. intro loaded.
  apply VMCacheConfig.preserves_bind; [exact IH|]. intro outputs. apply VMCacheConfig.preserves_ret.
Qed.

Theorem fill_from_entries_step_batch imem mem time entries cache :
  TLB.fill_from_entries_step imem mem time entries cache =
    (targets ← mapM (entry_targets imem mem time (TLB.pte_present cache)) entries;
      fill_batch time keep_table (List.concat targets) cache).
Proof.
  revert cache. induction entries as [|entry entries IH]; intro cache; [reflexivity|].
  unfold TLB.fill_from_entries_step at 1. cbn [mapM].
  unfold fmap, st_fmap, result_fmap, mbind, st_bind, result_bind.
  rewrite fill_from_entry_batch.
  destruct (entry_targets imem mem time (TLB.pte_present cache) entry) as [targets|err] eqn:Hexpand;
    [|reflexivity]. cbn [mbind result_bind].
  destruct (fill_batch_total time keep_table targets cache) as [mid [outputs Hbatch]].
  rewrite Hbatch. cbn.
  pose proof (fill_batch_config time keep_table targets cache mid outputs Hbatch) as Hconfig.
  unfold VMCacheConfig.config in Hconfig. assert (Hpresent : TLB.pte_present mid = TLB.pte_present cache) by congruence.
  pose proof (IH mid) as Htail. rewrite Hpresent in Htail.
  destruct (mapM (entry_targets imem mem time (TLB.pte_present cache)) entries)
    as [target_lists|err] eqn:Htargets.
  - cbn in Htail |- *. rewrite fill_batch_app. unfold mbind, st_bind, result_bind. rewrite Hbatch. cbn.
    rewrite <- Htail. unfold TLB.fill_from_entries_step, fmap, st_fmap, result_fmap.
    destruct (mapM (TLB.fill_from_entry imem mem time) entries mid) as [[last outputs']|err]; reflexivity.
  - cbn in Htail. unfold TLB.fill_from_entries_step, fmap, st_fmap, result_fmap in Htail |- *.
    destruct (mapM (TLB.fill_from_entry imem mem time) entries mid) as [[last outputs']|err'];
      [discriminate|]. exact Htail.
Qed.

Lemma mapM_permutation {A B} (f : A → result string B) first second :
  first ≡ₚ second → ∀ outputs, mapM f first = Ok outputs →
  ∃ outputs', mapM f second = Ok outputs' ∧ outputs ≡ₚ outputs'.
Proof.
  intro Hperm. induction Hperm as [|entry first second Hperm IH|
    first second rest|first middle second Hleft IHleft Hright IHright]; intros outputs Hrun.
  - exists outputs. split; [exact Hrun|apply Permutation_refl].
  - cbn [mapM] in Hrun |- *. unfold mbind, result_bind in Hrun |- *.
    destruct (f entry) as [output|err]; [|discriminate].
    destruct (mapM f first) as [tail|err] eqn:Htail; [|discriminate].
    injection Hrun as <-. destruct (IH tail eq_refl) as [tail' [Htail' Hperm']].
    rewrite Htail'. exists (output :: tail'). split; [reflexivity|apply perm_skip, Hperm'].
  - cbn [mapM] in Hrun |- *. unfold mbind, result_bind in Hrun |- *.
    destruct (f second) as [output2|err]; [|discriminate].
    destruct (f first) as [output1|err]; [|discriminate].
    destruct (mapM f rest) as [tail|err]; [|discriminate]. injection Hrun as <-.
    exists (output1 :: output2 :: tail). split; [reflexivity|apply perm_swap].
  - destruct (IHleft outputs Hrun) as [mid [Hmid Hperm1]].
    destruct (IHright mid Hmid) as [ending [Hend Hperm2]].
    exists ending. split; [exact Hend|eapply Permutation_trans; eassumption].
Qed.

Lemma concat_permutation {A} (first second : list (list A)) :
  first ≡ₚ second → List.concat first ≡ₚ List.concat second.
Proof.
  intro Hperm. induction Hperm; cbn [List.concat].
  - apply Permutation_refl.
  - apply Permutation_app_head, IHHperm.
  - rewrite !app_assoc. apply Permutation_app_tail, Permutation_app_comm.
  - eapply Permutation_trans; eassumption.
Qed.

Theorem fill_from_entries_step_permutation imem mem time entries entries' old new old' outputs :
  equiv old new → entries ≡ₚ entries' →
  TLB.fill_from_entries_step imem mem time entries old = Ok (old', outputs) →
  ∃ new' outputs', TLB.fill_from_entries_step imem mem time entries' new = Ok (new', outputs') ∧
    equiv old' new' ∧ outputs ≡ₚ outputs'.
Proof.
  intros Heq Hperm Hrun. rewrite fill_from_entries_step_batch in Hrun |- *.
  destruct (mapM (entry_targets imem mem time (TLB.pte_present old)) entries)
    as [targets|err] eqn:Htargets; [|discriminate]. cbn [mbind result_bind] in Hrun.
  destruct (mapM_permutation (entry_targets imem mem time (TLB.pte_present old)) entries entries'
    Hperm targets Htargets) as [targets' [Htargets' Hperm_targets]].
  destruct Heq as [Hpresent Hhistory]. rewrite <- Hpresent, Htargets'. cbn [mbind result_bind].
  destruct (fill_batch_permutation time keep_table (List.concat targets) (List.concat targets')
    (concat_permutation targets targets' Hperm_targets) old old' outputs Hrun)
    as [mid [outputs' [Hbatch [Heq1 Houtputs]]]].
  destruct (fill_batch_equiv time keep_table (List.concat targets') old new mid outputs'
    (conj Hpresent Hhistory) Hbatch) as [new' [Hbatch' Heq2]].
  exists new', outputs'. split; [exact Hbatch'|]. split;
    [eapply equiv_trans; eassumption|exact Houtputs].
Qed.


(** All three traversal levels agree even when parent lists arrive in a
    different order and dormant allocations differ between the caches. *)
Theorem fill_from_entries_permutation imem mem time entries entries' old new old' :
  equiv old new → entries ≡ₚ entries' →
  TLB.fill_from_entries imem mem time entries old = Ok (old', ()) →
  ∃ new', TLB.fill_from_entries imem mem time entries' new = Ok (new', ()) ∧ equiv old' new'.
Proof.
  intros Heq Hperm Hrun. unfold TLB.fill_from_entries in Hrun |- *.
  unfold mbind, st_bind, result_bind in Hrun |- *.
  destruct (TLB.fill_from_entries_step imem mem time entries old) as [[mid1 entries1]|err] eqn:Hfirst;
    [|discriminate]. cbn in Hrun.
  destruct (TLB.fill_from_entries_step imem mem time entries1 mid1) as [[mid2 entries2]|err] eqn:Hsecond;
    [|discriminate]. cbn in Hrun.
  destruct (TLB.fill_from_entries_step imem mem time entries2 mid2) as [[mid3 entries3]|err] eqn:Hthird;
    [|discriminate]. cbn in Hrun.
  destruct (fill_from_entries_step_permutation imem mem time entries entries' old new mid1 entries1
    Heq Hperm Hfirst) as [next1 [targets1 [Hfirst' [Heq1 Hperm1]]]].
  destruct (fill_from_entries_step_permutation imem mem time entries1 targets1 mid1 next1 mid2 entries2
    Heq1 Hperm1 Hsecond) as [next2 [targets2 [Hsecond' [Heq2 Hperm2]]]].
  destruct (fill_from_entries_step_permutation imem mem time entries2 targets2 mid2 next2 mid3 entries3
    Heq2 Hperm2 Hthird) as [next3 [targets3 [Hthird' [Heq3 Hperm3]]]].
  unfold guard_or', guard_or in Hrun.
  destruct (decide (entries3 = [])) as [Hnil|Hnil]; [|discriminate].
  change (@Ok string _ (mid3, ()) = Ok (old', ())) in Hrun. injection Hrun as <-.
  rewrite Hnil in Hperm3. apply Permutation_nil in Hperm3. subst targets3.
  rewrite Hfirst'. cbn. rewrite Hsecond'. cbn. rewrite Hthird'. cbn.
  exists next3. split; [|exact Heq3].
  reflexivity.
Qed.

End VMCacheTraversal.
