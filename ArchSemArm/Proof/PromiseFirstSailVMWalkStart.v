(******************************************************************************)
(* The translation start replayed up to walk addresses                       *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From SailStdpp Require Import ConcurrencyInterfaceBuiltinsV2.
From SailTinyArm Require Import System.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstSailCurrent PromiseFirstVMExecutionCurrent PromiseFirstSailRead
  PromiseFirstSailVMViews PromiseFirstSailVMCacheSim PromiseFirstSailVMMerge
  PromiseFirstSailVMTransEnd PromiseFirstSailVMTranslation PromiseFirstSailVMGuards
  PromiseFirstSailVMCacheConfig PromiseFirstSailVMLookup PromiseFirstSailVMBounds
  PromiseFirstSailVMDirect PromiseFirstSailVMNormalization PromiseFirstSailNoFuel
  PromiseFirstSailVMInstructionReplay PromiseFirstSailVMCreatingReplay
  PromiseFirstSailVMWalkSail PromiseFirstSailVMWalkReplay PromiseFirstSailVMCreatingWalk
  PromiseFirstSailVMEventValidity.
#[local] Open Scope stdpp.

(** The translation-start obligations [VMWalkReplay.StepStartW] and
    [VMCreatingWalk.StepStartOwnW] from two lookup-level premises.

    - [LookupBi]: delivering the event to a thread state relates the TLB
      lookups in both directions. Each original result has a replay with the
      same root, walk and start; each replay result that starts by the end of
      the original history replays an original result. For a foreign event
      the end may grow from the original bound to the new bound and an
      absent invalidation deadline may become one beyond the history; for an
      own event both are unchanged.
    - [LookupShaped]: every lookup result of the original thread state walks
      through table descriptors ([shaped]), carried as the invariant [Sh] of
      [VMWalkReplay.ShInvariant].

    From these, the merged result chosen by the original translation start
    has a merged replay with the same start, a related end and deadline, the
    same leaf and the same non-address table bits ([merge_replay_exact]);
    the walks are related by [VMWalkReplay.prel] ([prel_of_key], using
    [table_rel_at]), and the translation start replays ([step_start_f],
    [step_start_own]). *)

Module VMWalkStart.
Import VMWalkSail.

(** * Descriptors that differ only in table addresses *)


Lemma tb_byte z k i : (0 ≤ k → 0 ≤ i →
  Z.testbit (Z.shiftl (bv_wrap 8 (Z.shiftr z k)) k) i = bool_decide (k ≤ i < k + 8) && Z.testbit z i)%Z.
Proof.
  intros Hk Hi. rewrite Z.shiftl_spec by lia.
  destruct (decide (i < k)%Z).
  - rewrite Z.testbit_neg_r by lia. rewrite bool_decide_false by lia. reflexivity.
  - rewrite bv_wrap_spec, Z.shiftr_spec by lia. replace (i - k + k)%Z with i by lia.
    repeat case_bool_decide; try lia; reflexivity.
Qed.

Lemma conv_id v : conv v = v.
Proof.
  unfold conv, from_bytes_le, System_types.Defs.bytes_of_bv.
  unfold SailStdpp.Values.foreach_Z_up. cbn [SailStdpp.Values.foreach_Z_up' Z.abs_nat Z.sub Z.add Z.opp Pos.to_nat].
  cbv -[bv_extract bv_concat bv_0 bv_unsigned].
  apply bv_eq. bv_simplify. cbn [Z.of_N].
  apply Z.bits_inj_iff'. intros i Hi.
  rewrite !Z.lor_spec.
  replace (Z.shiftl (bv_wrap 8 (bv_unsigned v)) 0) with (Z.shiftl (bv_wrap 8 (Z.shiftr (bv_unsigned v) 0)) 0) by (rewrite Z.shiftr_0_r; reflexivity).
  rewrite !tb_byte by lia.
  destruct (decide (i < 64)%Z).
  - repeat case_bool_decide; try lia; cbn [andb orb];
      destruct (Z.testbit (bv_unsigned v) i); reflexivity.
  - rewrite bv_unsigned_spec_high by lia.
    repeat case_bool_decide; try lia; reflexivity.
Qed.

Lemma extract_compose (x : bv 64) a k s l :
  (a ≤ s)%N → (s + l ≤ a + k)%N → (a + k ≤ 64)%N →
  bv_extract s l x = bv_extract (s - a) l (bv_extract a k x).
Proof.
  intros. apply bv_eq. rewrite !bv_extract_unsigned.
  apply Z.bits_inj_iff'. intros i Hi.
  rewrite !bv_wrap_spec, !Z.shiftr_spec by lia.
  rewrite bv_wrap_spec by lia. rewrite Z.shiftr_spec by lia.
  repeat case_bool_decide; try lia; cbn [andb]; try reflexivity.
  f_equal. lia.
Qed.

Lemma table_rel_at (lvl : nat) (x1 x2 : bv 64) : (lvl < 3)%nat → bv_extract 0 2 x1 = 3%bv →
  TLB.Result.table_attrs x1 = TLB.Result.table_attrs x2 → rel_at lvl x1 x2.
Proof.
  intros Hlvl Hb Ha. unfold TLB.Result.table_attrs in Ha. pose proof (f_equal fst Ha) as Hlo. pose proof (f_equal snd Ha) as Hhi. cbn in Hlo, Hhi. clear Ha.
  right. rewrite !conv_id.
  assert (Hb2 : bv_extract 0 2 x2 = 3%bv).
  { rewrite (extract_compose x2 0 12) by lia. rewrite <- Hlo, <- (extract_compose x1 0 12) by lia. exact Hb. }
  assert (E0 : ∀ x : bv 64, bv_extract 0 2 x = 3%bv → bv_extract 0 1 x = 1%bv ∧ bv_extract 1 1 x = 1%bv).
  { intros x Hx. rewrite (extract_compose x 0 2 0 1), (extract_compose x 0 2 1 1) by lia.
    rewrite Hx. split; apply bv_eq; reflexivity. }
  assert (Hhi' : ∀ s l, (48 ≤ s)%N → (s + l ≤ 64)%N → bv_extract s l x1 = bv_extract s l x2).
  { intros s l ? ?. rewrite (extract_compose x1 48 16), (extract_compose x2 48 16) by lia.
    rewrite Hhi. reflexivity. }
  destruct (E0 x1 Hb) as [A0 A1]. destruct (E0 x2 Hb2) as [B0 B1].
  assert (Hd : ∀ x : bv 64, bv_extract 0 1 x = 1%bv → bv_extract 1 1 x = 1%bv →
    decode_desc_type x (Z.of_nat lvl) = DescriptorType_Table).
  { intros x H0 H1. unfold decode_desc_type.
    change (@Operators_mwords.access_vec_dec 64 x 0) with (bv_extract 0 1 x).
    change (@Operators_mwords.access_vec_dec 64 x 1) with (bv_extract 1 1 x).
    rewrite H0, H1. destruct lvl as [|[|[|]]]; [reflexivity..|lia]. }
  split; [apply Hd; assumption|]. split; [apply Hd; assumption|].
  unfold extract_perms_table. f_equal.
  - f_equal. f_equal. unfold Operators_mwords.subrange_vec_dec. f_equal. f_equal.
    apply Hhi'; vm_compute; congruence.
  - f_equal. f_equal. unfold Operators_mwords.subrange_vec_dec. f_equal. f_equal.
    apply Hhi'; vm_compute; congruence.
  - f_equal. change (@Operators_mwords.access_vec_dec 64 x1 60) with (bv_extract 60 1 x1).
    change (@Operators_mwords.access_vec_dec 64 x2 60) with (bv_extract 60 1 x2). apply Hhi'; lia.
  - f_equal. change (@Operators_mwords.access_vec_dec 64 x1 59) with (bv_extract 59 1 x1).
    change (@Operators_mwords.access_vec_dec 64 x2 59) with (bv_extract 59 1 x2). apply Hhi'; lia.
Qed.

#[local] Open Scope nat_scope.
Import VMPromising VMCacheSim VMInstructionReplay VMWalkReplay VMCreatingWalk.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

(** * Paths of table descriptors *)

(** Every descriptor of [path] but the last is a table descriptor at its
    level, counting levels from [lvl]. *)
Definition shaped (lvl : nat) (path : list (bv 64)) : Prop :=
  ∀ i x, S i < length path → path !! i = Some x → lvl + i < 3 ∧ bv_extract 0 2 x = 3%bv.

Lemma shaped_tail lvl x path : shaped lvl (x :: path) → shaped (S lvl) path.
Proof.
  intros H i y Hi Hy. destruct (H (S i) y ltac:(cbn; lia) Hy) as [Hl Hb]. split; [lia|exact Hb].
Qed.

Lemma prel_of_key lvl (p1 p2 : list (bv 64)) :
  shaped lvl p1 → last p1 = last p2 →
  map TLB.Result.table_attrs (removelast p1) = map TLB.Result.table_attrs (removelast p2) →
  prel lvl p1 p2.
Proof.
  revert lvl p2. induction p1 as [|x p1 IH]; intros lvl p2 Hs Hl Ht.
  - destruct p2 as [|y p2]; [exact I|]. exfalso. cbn in Hl.
    rewrite last_cons in Hl. destruct (last p2); discriminate.
  - destruct p2 as [|y p2]; [rewrite last_cons in Hl; destruct (last p1); discriminate|].
    destruct p1 as [|x' p1].
    + destruct p2 as [|y' p2]; cbn in Hl, Ht |- *.
      * injection Hl as ->. split; [left; reflexivity|exact I].
      * exfalso. discriminate Ht.
    + destruct p2 as [|y' p2].
      * exfalso. cbn in Ht. discriminate Ht.
      * change (removelast (x :: x' :: p1)) with (x :: removelast (x' :: p1)) in Ht.
        change (removelast (y :: y' :: p2)) with (y :: removelast (y' :: p2)) in Ht.
        cbn [map] in Ht.
        pose proof (f_equal (λ l, default (TLB.Result.table_attrs x) (head l)) Ht) as Hxy.
        apply (f_equal List.tl) in Ht. cbn [head default List.tl] in Hxy, Ht.
        rewrite !last_cons_cons in Hl.
        change (rel_at lvl x y ∧ prel (S lvl) (x' :: p1) (y' :: p2)). split.
        -- destruct (Hs 0 x ltac:(cbn; lia) eq_refl) as [Hlvl Hb].
           apply table_rel_at; [lia|exact Hb|exact Hxy].
        -- apply IH; [eapply shaped_tail; exact Hs|exact Hl|exact Ht].
Qed.

(** * Merging related lookup results *)

Section MergeRel.
Local Notation key := VMCacheSim.key.

Definition ti (r : TLB.Result.t) := (TLB.Result.tend r, TLB.Result.inv_time r).

(** [r'] is a replay of [r]: same walk and start, and the end and
    invalidation deadline related by [TI]. *)
Definition res_rel (TI : nat * option nat → nat * option nat → Prop) (r r' : TLB.Result.t) :=
  TLB.Result.ttbr r' = TLB.Result.ttbr r ∧ TLB.Result.path r' = TLB.Result.path r ∧
  TLB.Result.tstart r' = TLB.Result.tstart r ∧ TI (ti r) (ti r').

Lemma merge_unique (l : list TLB.Result.t) m m2 :
  m ∈ TLB.Result.merge l → m2 ∈ TLB.Result.merge l → key m2 = key m → m2 = m.
Proof.
  intros Hm Hm2 Hk. pose proof (VMCacheSim.merge_nodup l [] (NoDup_nil_2)) as Hnd.
  pose proof (VMCacheSim.elem_find_key _ _ Hnd Hm) as H1.
  pose proof (VMCacheSim.elem_find_key _ _ Hnd Hm2) as H2.
  unfold TLB.Result.merge in *. rewrite Hk in H2. congruence.
Qed.

Lemma key_ti r : ti r = ((key r).1.2, (key r).2).
Proof. reflexivity. Qed.

Theorem merge_replay_exact TI (bound : nat) (olds news : list TLB.Result.t) :
  (∀ r1 r2 b, r1 ∈ olds → r2 ∈ olds → TI (ti r1) b → TI (ti r2) b → ti r1 = ti r2) →
  (∀ r, r ∈ olds → TLB.Result.tstart r ≤ bound) →
  (∀ r, r ∈ olds → ∃ r', r' ∈ news ∧ res_rel TI r r') →
  (∀ r', r' ∈ news → TLB.Result.tstart r' ≤ bound → ∃ r, r ∈ olds ∧ res_rel TI r r') →
  ∀ m, m ∈ TLB.Result.merge olds → ∃ m', m' ∈ TLB.Result.merge news ∧
    TLB.Result.tstart m' = TLB.Result.tstart m ∧ TI (ti m) (ti m') ∧
    last (TLB.Result.path m') = last (TLB.Result.path m) ∧
    map TLB.Result.table_attrs (removelast (TLB.Result.path m')) =
      map TLB.Result.table_attrs (removelast (TLB.Result.path m)).
Proof.
  intros Hinj Hbound Hfwd Hbwd m Hm.
  destruct (VMMergeReplay.merge_witness olds m Hm) as (s & Hs & Hms & Hts).
  destruct (Hfwd s Hs) as (s' & Hs' & _ & Hps & Hss & Hti).
  destruct (VMMergeReplay.merge_covers news s' Hs') as (m' & Hm' & Hm's' & Hts').
  destruct (VMMergeReplay.merge_witness news m' Hm') as (r' & Hr' & Hm'r' & Htr').
  apply VMCacheSim.mergeable_key in Hms, Hm's', Hm'r'.
  assert (Hle : TLB.Result.tstart m' ≤ TLB.Result.tstart m) by lia.
  destruct (decide (TLB.Result.tstart r' ≤ bound)) as [Hr'b|Hr'b];
    [|exfalso; pose proof (Hbound s Hs); lia].
  destruct (Hbwd r' Hr' Hr'b) as (r & Hr & _ & Hpr & Hsr & Htir).
  assert (Hkey : key r = key s).
  { assert (Hk : key s' = key r') by congruence.
    assert (Hti' : ti s' = ti r') by (rewrite !key_ti, Hk; reflexivity).
    rewrite Hti' in Hti. pose proof (Hinj r s _ Hr Hs Htir Hti) as Htirs.
    unfold key in Hk |- *. unfold ti in Htirs.
    pose proof (f_equal fst Htirs) as E1. pose proof (f_equal snd Htirs) as E2. cbn in E1, E2.
    rewrite E1, E2, <- Hpr, <- Hps.
    pose proof (f_equal (λ k, k.1.1) Hk) as E3. cbn in E3. rewrite E3. reflexivity. }
  destruct (VMMergeReplay.merge_covers olds r Hr) as (m2 & Hm2 & Hm2r & Htm2).
  apply VMCacheSim.mergeable_key in Hm2r.
  assert (Hm2m : m2 = m) by (apply (merge_unique olds); [exact Hm|exact Hm2|congruence]).
  subst m2.
  exists m'. split; [exact Hm'|]. split; [lia|].
  assert (Hk : key m' = key s') by exact Hm's'.
  unfold key in Hk, Hms. injection Hk as Hk1 Hk2 Hk3 Hk4. injection Hms as Hl1 Hl2 Hl3 Hl4.
  rewrite Hps in Hk1, Hk2.
  split; [unfold ti; rewrite Hk3, Hk4, Hl3, Hl4; exact Hti|].
  split; congruence.
Qed.
End MergeRel.

(** * The translation start as a relation on states *)

Section Char.
Context (tid : nat) (imem : memoryMap).

Definition ts_ifetch (s : TranslationStartInfo) : bool :=
  (AccessDescriptor_acctype (TranslationStartInfo_accdesc s) =? AccessType_IFETCH)%stdpp.
Definition ts_vpre s ts iis : nat :=
  TState.vcse ts ⊔ IIS.strict iis ⊔ view_if (TState.ets2 ts && negb (ts_ifetch s)) (TState.vdsb ts).
Definition ts_vinv s ts iis : nat :=
  ts_vpre s ts iis ⊔ view_if (TState.ets2 ts) (TState.vwr ts ⊔ TState.vrd ts).
Definition ts_vmax (m : list Ev.t) ts : nat := pred (TState.min_promise (length m) ts).
Definition ts_offs s :=
  TState.va_page_offsets (TranslationStartInfo_va s) (Z.to_N (TranslationStartInfo_size s)).

(** The translation result and invalidation deadline chosen by a translation
    start, with the instruction state after the TTBR0 read. *)
Definition TSOut s ts (m : list Ev.t) iis tres (inv : option nat) iis1 : Prop :=
  (is_upper_va (TranslationStartInfo_va s) = None ∧
    tres = IIS.TransRes.make (ts_vpre s ts iis) (ts_vmax m ts) None [] ∧ inv = None ∧ iis1 = iis) ∨
  (∃ upper reg_ttbr ttbr0 vw res val_ttbr,
    is_upper_va (TranslationStartInfo_va s) = Some upper ∧
    root_ttbr (TranslationStartInfo_regime s) upper = Ok reg_ttbr ∧
    Exec.elem_of_results ((ts, iis1), (ttbr0, vw)) (read_sreg_indirect TTBR0_EL1 None (ts, iis)) ∧
    TranslationStartInfo_asid s = bv_extract 48 16 ttbr0 ∧
    res ∈ TLB.Result.merge (Exec.results (TState.tlb_lookup tid imem m ts (ts_ifetch s) upper
      (va_to_vpn (TranslationStartInfo_va s)) (TranslationStartInfo_asid s) ttbr0
      (ts_vpre s ts iis) (ts_vinv s ts iis) (ts_vmax m ts))) ∧
    val_to_regval reg_ttbr (TLB.Result.ttbr res) = Some val_ttbr ∧
    tres = IIS.TransRes.make (TLB.Result.tstart res) (TLB.Result.tend res)
      (Some (existT reg_ttbr val_ttbr)) (TLB.Result.path res) ∧
    inv = TLB.Result.inv_time res).

Lemma ts_elim s ts m iis p' :
  Exec.elem_of_results (p', ()) (run_trans_start tid imem s (PPState.Make ts m iis)) →
  TranslationStartInfo_regime s = Regime_EL10 ∧ ts_vpre s ts iis ≤ ts_vmax m ts ∧
  ∃ tres inv iis1, TSOut s ts m iis tres inv iis1 ∧
    TState.tcohs_before_inv_time (TranslationStartInfo_asid s) (ts_offs s) inv ts ∧
    p' = PPState.Make (TState.update_tcohs (TranslationStartInfo_asid s) (ts_offs s)
      (IIS.TransRes.trans_start tres) ts) m (IIS.set_inv_time inv (IIS.set_trs tres iis1)).
Proof.
  intro Hrun. unfold run_trans_start in Hrun. VMViews.invert.
  all: try match goal with H : Exec.elem_of_results (?x, ?vv) (read_sreg_indirect ?rg ?ra ?st) |- _ =>
    pose proof (VMTLBShape.read_sreg_indirect_fst rg ra st x vv H) as Hx;
    destruct x as [ts3 iis3]; cbn in Hx; subst ts3 end.
  all: cbn [PPState.state PPState.mem PPState.iis] in *.
  all: repeat match goal with H : ?a = ?b |- _ => is_var a; is_var b; subst a end.
  all: split; [assumption|]; split; [assumption|].
  - do 3 eexists. split; [right; do 6 eexists; split; [eassumption|]; split; [eassumption|];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
      split; [eassumption|]; split; reflexivity|].
    split; [assumption|]. reflexivity.
  - do 3 eexists. split; [left; split; [eassumption|]; split; [reflexivity|]; split; reflexivity|].
    split; [assumption|]. reflexivity.
Qed.

Lemma ts_intro s ts m iis tres inv iis1 :
  TranslationStartInfo_regime s = Regime_EL10 → ts_vpre s ts iis ≤ ts_vmax m ts →
  TSOut s ts m iis tres inv iis1 →
  TState.tcohs_before_inv_time (TranslationStartInfo_asid s) (ts_offs s) inv ts →
  Exec.elem_of_results (PPState.Make (TState.update_tcohs (TranslationStartInfo_asid s) (ts_offs s)
      (IIS.TransRes.trans_start tres) ts) m (IIS.set_inv_time inv (IIS.set_trs tres iis1)), ())
    (run_trans_start tid imem s (PPState.Make ts m iis)).
Proof.
  intros Hreg Hguard Hout Htcoh. unfold run_trans_start.
  do 3 (eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]). cbn [PPState.state PPState.mem PPState.iis].
  apply exec_guard_or_bind_intro; [exact Hreg|].
  apply guard_discard_bind_intro; [exact Hguard|]. intros _.
  eapply Exec.elem_of_bind_intro with (a := (tres, inv)) (st' := PPState.Make ts m iis1).
  - destruct Hout as [(Hnone & -> & -> & ->)|(upper & reg_ttbr & ttbr0 & vw & res & val_ttbr & Hup &
      Hroot & Hread & Hasid & Hres & Hval & -> & ->)].
    + rewrite Hnone. apply Exec.elem_of_mret.
    + rewrite Hup.
      eapply Exec.elem_of_bind_intro; [apply exec_lift_result; exact Hroot|]. cbv beta.
      eapply Exec.elem_of_bind_intro;
        [exact (Exec.elem_of_liftSt (PPState.Make ts m iis) (ts, iis1) (ttbr0, vw)
          (PPState.state ×× PPState.iis) _ Hread)|].
      cbv beta iota.
      apply exec_guard_or_bind_intro; [exact Hasid|].
      apply exec_guard_or_bind_intro.
      { intro Hnil. exfalso. cbn [Exec.results] in Hnil. rewrite Hnil in Hres. inversion Hres. }
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_lift_res; exact Hres|]. cbv beta.
      rewrite Hval. cbn [othrow]. apply Exec.elem_of_mret.
  - cbv beta iota.
    apply guard_discard_bind_intro; [exact Htcoh|]. intros _.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
    match goal with |- Exec.elem_of_results (?a, ?r) ?e =>
      assert (Hs : ∀ b, b = a → Exec.elem_of_results (b, r) e → Exec.elem_of_results (a, r) e)
        by (intros b ->; exact id) end.
    eapply Hs; [|apply Exec.elem_of_mset]. reflexivity.
Qed.
End Char.

(** * Lookup-level premises *)

Definition TIf (bound tmax tmax' : nat) (a b : nat * option nat) : Prop :=
  (b.1 = a.1 ∨ (a.1 = tmax ∧ b.1 = tmax')) ∧
  (b.2 = a.2 ∨ (a.2 = None ∧ ∃ t, bound < t ∧ b.2 = Some t)).

(** Delivering [ev] to a thread state relates its lookups in both
    directions: each original result has a replay with the same root, walk
    and start; each replay result starting by the end of the original
    history replays an original one. End and invalidation deadline are
    related by [TIf] for a foreign event and equal for an own event. *)
Definition LookupBi (tid : nat) imem mem ev (own : bool) : Prop :=
  ∀ ts issued ifetch upper vpn asid ttbr0 tmin_ok tmin_unc,
    VMViews.ts_ok (length mem) ts → (own = true → Ev.tid ev = tid) →
    TState.emit_promise tid imem (ev :: mem) ev ts = Ok issued →
    tmin_ok ≤ pred (TState.min_promise (length mem) ts) → tmin_ok ≤ tmin_unc →
    let tmax := pred (TState.min_promise (length mem) ts) in
    let tmax' := pred (TState.min_promise (length (ev :: mem)) issued) in
    let olds := Exec.results (TState.tlb_lookup tid imem mem ts ifetch upper vpn asid ttbr0
      tmin_ok tmin_unc tmax) in
    let news := Exec.results (TState.tlb_lookup tid imem (ev :: mem) issued ifetch upper vpn asid
      ttbr0 tmin_ok tmin_unc tmax') in
    let TI := if own then eq else TIf (length mem) tmax tmax' in
    tmax ≤ tmax' ∧
    (∀ r, r ∈ olds → TLB.Result.tstart r ≤ length mem ∧ TLB.Result.tend r ≤ tmax ∧
      VMViews.le_opt (length mem) (TLB.Result.inv_time r)) ∧
    (∀ r, r ∈ olds → ∃ r', r' ∈ news ∧ res_rel TI r r') ∧
    (∀ r', r' ∈ news → TLB.Result.tstart r' ≤ length mem → ∃ r, r ∈ olds ∧ res_rel TI r r').

(** Every lookup result of the thread state walks through table descriptors. *)
Definition LookupShaped (tid : nat) imem mem ts : Prop :=
  ∀ ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax r,
    r ∈ Exec.results (TState.tlb_lookup tid imem mem ts ifetch upper vpn asid ttbr0
      tmin_ok tmin_unc tmax) →
    shaped 0 (TLB.Result.path r).

Lemma merge_into_src r acc x : x ∈ TLB.Result.merge_into r acc →
  ∃ y, y ∈ r :: acc ∧ TLB.Result.path x = TLB.Result.path y.
Proof.
  induction acc as [|a acc IH]; cbn [TLB.Result.merge_into]; intro Hx.
  - apply list_elem_of_singleton in Hx as ->. exists r. split; [left|reflexivity].
  - case_decide.
    + apply elem_of_cons in Hx as [->|Hx].
      * destruct (TLB.Result.walk_lt _ _); [exists r|exists a]; (split; [set_solver|reflexivity]).
      * exists x. split; [set_solver|reflexivity].
    + apply elem_of_cons in Hx as [Hx|Hx]; [subst; exists a; split; [set_solver|reflexivity]|].
      destruct (IH Hx) as (y & Hy & Hp). exists y. split; [set_solver|exact Hp].
Qed.

Lemma merge_src l x : x ∈ TLB.Result.merge l → ∃ y, y ∈ l ∧ TLB.Result.path x = TLB.Result.path y.
Proof.
  unfold TLB.Result.merge. cut (∀ acc, x ∈ foldl (λ acc r, TLB.Result.merge_into r acc) acc l →
    ∃ y, y ∈ (acc ++ l)%list ∧ TLB.Result.path x = TLB.Result.path y).
  { intros H Hx. destruct (H [] Hx) as (y & Hy & Hp). exists y. split; [exact Hy|exact Hp]. }
  induction l as [|r l IH]; intros acc Hx; cbn in Hx.
  - exists x. rewrite app_nil_r. split; [exact Hx|reflexivity].
  - destruct (IH _ Hx) as (y & Hy & Hp). apply elem_of_app in Hy as [Hy|Hy].
    + destruct (merge_into_src r acc y Hy) as (z & Hz & Hp'). exists z. split; [set_solver|congruence].
    + exists y. split; [set_solver|exact Hp].
Qed.

Section Merged.
Context (tid : nat) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t) (own : bool).

Lemma merged_bi (HB : LookupBi tid imem mem ev own) ts issued ifetch upper vpn asid ttbr0
    tmin_ok tmin_unc m :
  VMViews.ts_ok (length mem) ts → (own = true → Ev.tid ev = tid) →
  TState.emit_promise tid imem (ev :: mem) ev ts = Ok issued →
  tmin_ok ≤ pred (TState.min_promise (length mem) ts) → tmin_ok ≤ tmin_unc →
  m ∈ TLB.Result.merge (Exec.results (TState.tlb_lookup tid imem mem ts ifetch upper vpn asid ttbr0
      tmin_ok tmin_unc (pred (TState.min_promise (length mem) ts)))) →
  ∃ m', m' ∈ TLB.Result.merge (Exec.results (TState.tlb_lookup tid imem (ev :: mem) issued ifetch
      upper vpn asid ttbr0 tmin_ok tmin_unc (pred (TState.min_promise (length (ev :: mem)) issued)))) ∧
    TLB.Result.tstart m' = TLB.Result.tstart m ∧
    (if own then @eq (nat * option nat) else TIf (length mem) (pred (TState.min_promise (length mem) ts))
      (pred (TState.min_promise (length (ev :: mem)) issued))) (ti m) (ti m') ∧
    last (TLB.Result.path m') = last (TLB.Result.path m) ∧
    map TLB.Result.table_attrs (removelast (TLB.Result.path m')) =
      map TLB.Result.table_attrs (removelast (TLB.Result.path m)).
Proof.
  intros Hts Hown He Hmin Hunc Hm.
  destruct (HB ts issued ifetch upper vpn asid ttbr0 tmin_ok tmin_unc Hts Hown He Hmin Hunc)
    as (Hle & Hfacts & Hfwd & Hbwd).
  eapply (merge_replay_exact _ (length mem)); [| |exact Hfwd|exact Hbwd|exact Hm].
  - intros r1 r2 b H1 H2 T1 T2. destruct own; [congruence|].
    destruct (Hfacts r1 H1) as (_ & E1 & I1). destruct (Hfacts r2 H2) as (_ & E2 & I2).
    destruct T1 as [A1 B1], T2 as [A2 B2]. unfold ti in *. cbn in *.
    f_equal.
    + destruct A1 as [A1|[A1 A1']], A2 as [A2|[A2 A2']]; lia.
    + destruct B1 as [B1|(B1 & t1 & Ht1 & B1')], B2 as [B2|(B2 & t2 & Ht2 & B2')]; try congruence.
      all: exfalso; first [rewrite B2' in B1; specialize (I1 t2 (eq_sym B1)); lia
        |rewrite B1' in B2; specialize (I2 t1 (eq_sym B2)); lia].
  - intros r Hr. exact (proj1 (Hfacts r Hr)).
Qed.
End Merged.

Section Helpers.
Context (W T : list nat) (C : option TLB.t).
Local Notation F := (VMTransEndReplay.frame W T C).

Lemma frame_tcohs a o v ts : TState.update_tcohs a o v (F ts) = F (TState.update_tcohs a o v ts).
Proof.
  unfold TState.update_tcohs. induction o as [|x o IH]; [reflexivity|].
  cbn [foldr]. rewrite IH. reflexivity.
Qed.

Lemma prom_tcohs a o v ts :
  TState.prom_wr (TState.update_tcohs a o v ts) = TState.prom_wr ts ∧
  TState.prom_tlbi (TState.update_tcohs a o v ts) = TState.prom_tlbi ts.
Proof.
  unfold TState.update_tcohs. induction o as [|x o IH]; [split; reflexivity|]. exact IH.
Qed.

Lemma emit_tcohs tid imem mem ev ts a o v :
  TState.emit_promise tid imem (ev :: mem) ev ts = Ok (F ts) →
  TState.emit_promise tid imem (ev :: mem) ev (TState.update_tcohs a o v ts) =
    Ok (F (TState.update_tcohs a o v ts)).
Proof.
  intro He. destruct (prom_tcohs a o v ts) as [Hw Hb].
  rewrite (VMEmit.emit_transfer tid imem mem ev ts _ _ He (VMTLBShape.tlb_update_tcohs a o v ts) Hw Hb).
  reflexivity.
Qed.
End Helpers.

Lemma tcoh_bound bound ts a (offs : list (bv 12)) :
  VMViews.ts_ok bound ts → ∀ off, off ∈ offs → TState.get_tcoh a off ts ≤ bound.
Proof.
  intros Hts off _. unfold TState.get_tcoh. rewrite lookup_total_alt.
  destruct (TState.tcoh ts !! (a, off)) as [t|] eqn:Ht; cbn; [|lia].
  exact (VMViews.ok_tcoh _ _ Hts _ _ Ht).
Qed.

Lemma root_ttbr_is regime upper r : root_ttbr regime upper = Ok r → is_ttbr r.
Proof.
  destruct regime; cbn; try discriminate. destruct upper; intro H; injection H as <-;
    [right|left]; reflexivity.
Qed.

Lemma val_ttbr_some r v : is_ttbr r → ∃ x, val_to_regval r v = Some x.
Proof.
  intros [-> | ->]; eexists; first [simp val_to_regval; reflexivity|vm_compute; reflexivity].
Qed.

Lemma unc_le s ts iis : ts_vpre s ts iis ≤ ts_vinv s ts iis.
Proof. unfold ts_vinv. apply Nat.le_max_l. Qed.

Section Step.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

Lemma step_start_f (HB : LookupBi tid imem mem ev false) s p p' r q0 :
  VMViews.ok p → Exact tid imem mem ev p q0 → LookupShaped tid imem mem (PPState.state p) →
  Exec.elem_of_results (p', r) (run_outcome n tid imem (TranslationStart s) p) →
  ∃ q0' v rr, Exec.elem_of_results (q0', r) (run_outcome n tid imem (TranslationStart s) q0) ∧
    is_ttbr rr ∧ Exact tid imem mem ev p' v ∧ SR rr 0 v q0'.
Proof.
  intros Hok Hex Hsh Hrun. destruct p as [ts m iis].
  destruct Hex as [Hm [issued [stop [inv0 [He [Hstop [Hinv0 ->]]]]]]].
  cbn [PPState.mem PPState.state PPState.iis] in Hm, He, Hstop, Hinv0, Hsh. subst m.
  destruct Hok as [Hts _]. cbn [PPState.mem PPState.state] in Hts.
  simp run_outcome in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [[] [Hstart Hret]]].
  apply Exec.elem_of_mret_inv in Hret as [-> ->].
  apply ts_elim in Hstart as (Hreg & Hg & tres & inv & iis1 & Hout & Htc & ->).
  pose proof (VMTransEndReplay.emit_promise_frame _ _ _ _ _ _ He) as Hframe.
  set (W := TState.prom_wr issued) in Hframe; set (T := TState.prom_tlbi issued) in Hframe;
    set (C := TState.tlb issued) in Hframe; clearbody W T C; subst issued.
  set (F := VMTransEndReplay.frame W T C) in *.
  set (Iv := VMTransEndReplay.interval_iis stop inv0).
  assert (Hets : TState.ets2 (F ts) = TState.ets2 ts)
    by exact (proj1 (VMCacheConfig.emit_promise_ets _ _ _ _ _ _ He)).
  assert (Hvpre : ts_vpre s (F ts) (Iv iis) = ts_vpre s ts iis)
    by (unfold ts_vpre; rewrite Hets; reflexivity).
  assert (Hvinv : ts_vinv s (F ts) (Iv iis) = ts_vinv s ts iis)
    by (unfold ts_vinv; rewrite Hvpre, Hets; reflexivity).
  pose proof (VMGuardReplay.emit_promise_translation_bound _ _ _ _ _ _ He) as Hmax.
  set (A := TranslationStartInfo_asid s) in *. set (O := ts_offs s) in *.
  assert (Hemit : ∀ v, TState.emit_promise tid imem (ev :: mem) ev (TState.update_tcohs A O v ts) =
      Ok (F (TState.update_tcohs A O v ts))) by (intro; apply emit_tcohs; exact He).
  pose proof (tcoh_bound _ _ A O Hts) as Htb.
  destruct Hout as [(Hnone & -> & -> & ->)|(upper & reg_ttbr & ttbr0 & vw & res & val_ttbr & Hup &
    Hroot & Hread & Hasid & Hres & Hval & -> & ->)].
  - set (tres' := IIS.TransRes.make (ts_vpre s (F ts) (Iv iis)) (ts_vmax (ev :: mem) (F ts)) None []).
    exists (PPState.Make (TState.update_tcohs A O (IIS.TransRes.trans_start tres') (F ts)) (ev :: mem)
      (IIS.set_inv_time None (IIS.set_trs tres' (Iv iis)))).
    exists (PPState.Make (F (TState.update_tcohs A O (ts_vpre s ts iis) ts)) (ev :: mem)
      (VMTransEndReplay.interval_iis (ts_vmax (ev :: mem) (F ts)) None
        (IIS.set_inv_time None (IIS.set_trs
          (IIS.TransRes.make (ts_vpre s ts iis) (ts_vmax mem ts) None []) iis)))).
    exists TTBR0_EL1.
    split; [|split; [left; reflexivity|split]].
    + simp run_outcome. eapply Exec.elem_of_bind_intro; [|apply Exec.elem_of_mret].
      apply ts_intro; [exact Hreg| |left; split; [exact Hnone|split; [reflexivity|split; reflexivity]]
        |exact Logic.I].
      rewrite Hvpre. unfold ts_vmax in *. cbn [length] in *. lia.
    + split; [reflexivity|].
      exists (F (TState.update_tcohs A O (ts_vpre s ts iis) ts)), (ts_vmax (ev :: mem) (F ts)), None.
      split; [apply Hemit|]. split.
      * intros trs Htrs. cbn in Htrs. injection Htrs as <-. cbn. unfold ts_vmax in *. lia.
      * split; [left; reflexivity|reflexivity].
    + eexists _, tres'. split; [reflexivity|]. split.
      * split; [cbn; rewrite Hvpre; reflexivity|]. split; [reflexivity|].
        split; [left; split; reflexivity|exact Logic.I].
      * cbn [IIS.TransRes.trans_start tres']. rewrite Hvpre. apply f_equal3; [apply frame_tcohs|reflexivity|].
        destruct iis; reflexivity.
  - assert (Hunc := unc_le s ts iis).
    destruct (merged_bi tid imem mem ev false HB ts (F ts) _ _ _ _ _ _ _ res Hts
      ltac:(discriminate) He Hg Hunc Hres) as (res' & Hres' & Hst & Hti & Hlast & Hattr).
    pose proof (root_ttbr_is _ _ _ Hroot) as Hrr.
    destruct (val_ttbr_some reg_ttbr (TLB.Result.ttbr res') Hrr) as [val' Hval'].
    set (tres' := IIS.TransRes.make (TLB.Result.tstart res') (TLB.Result.tend res')
      (Some (existT reg_ttbr val')) (TLB.Result.path res')).
    destruct Hti as [Hend Hinv]. unfold ti in Hend, Hinv. cbn [fst snd] in Hend, Hinv.
    assert (Hend' : TLB.Result.tend res ≤ TLB.Result.tend res') by (destruct Hend as [E|[E1 E2]]; lia).
    assert (Hinv' : VMTranslationReplay.inv_after (length mem) (TLB.Result.inv_time res)
        (TLB.Result.inv_time res')).
    { destruct Hinv as [E|(E1 & t & Ht & E2)]; [left; exact E|right; exists t; split; [lia|exact E2]]. }
    exists (PPState.Make (TState.update_tcohs A O (IIS.TransRes.trans_start tres') (F ts)) (ev :: mem)
      (IIS.set_inv_time (TLB.Result.inv_time res') (IIS.set_trs tres' (Iv iis1)))).
    exists (PPState.Make (F (TState.update_tcohs A O (TLB.Result.tstart res) ts)) (ev :: mem)
      (VMTransEndReplay.interval_iis (TLB.Result.tend res') (TLB.Result.inv_time res')
        (IIS.set_inv_time (TLB.Result.inv_time res) (IIS.set_trs
          (IIS.TransRes.make (TLB.Result.tstart res) (TLB.Result.tend res)
            (Some (existT reg_ttbr val_ttbr)) (TLB.Result.path res)) iis1)))).
    exists reg_ttbr.
    split; [|split; [exact Hrr|split]].
    + simp run_outcome. eapply Exec.elem_of_bind_intro; [|apply Exec.elem_of_mret].
      apply ts_intro; [exact Hreg| | |].
      * rewrite Hvpre. unfold ts_vmax in *. cbn [length] in *. lia.
      * right. exists upper, reg_ttbr, ttbr0, vw, res', val'.
        split; [exact Hup|]. split; [exact Hroot|].
        split; [exact (indirect_replay W T C stop inv0 TTBR0_EL1 None ts iis _ _ Hread)|].
        split; [exact Hasid|]. split; [rewrite Hvpre, Hvinv; exact Hres'|].
        split; [exact Hval'|]. split; reflexivity.
      * exact (VMTransEndReplay.tcohs_after_promise tid imem mem ev ts (F ts) A O
          (TLB.Result.inv_time res) (TLB.Result.inv_time res') He Htb Hinv' Htc).
    + split; [reflexivity|].
      exists (F (TState.update_tcohs A O (TLB.Result.tstart res) ts)), (TLB.Result.tend res'),
        (TLB.Result.inv_time res').
      split; [apply Hemit|]. split.
      * intros trs Htrs. cbn in Htrs. injection Htrs as <-. cbn. exact Hend'.
      * split; [exact Hinv'|reflexivity].
    + eexists _, tres'. split; [reflexivity|]. split.
      * split; [cbn; symmetry; exact Hst|]. split; [reflexivity|].
        split; [right; eexists _, _; split; reflexivity|].
        cbn [IIS.TransRes.remaining tres'].
        apply prel_of_key; [|symmetry; exact Hlast|symmetry; exact Hattr].
        destruct (merge_src _ _ Hres) as (y & Hy & Hp). rewrite Hp. eapply Hsh. exact Hy.
      * unfold tres'. cbn [IIS.TransRes.trans_start]. rewrite Hst. apply f_equal3; [apply frame_tcohs|reflexivity|].
        destruct iis1; reflexivity.
Qed.
End Step.

Lemma indirect_frame W T C reg racc ts iis st' vv :
  Exec.elem_of_results (st', vv) (read_sreg_indirect reg racc (ts, iis)) →
  Exec.elem_of_results ((VMTransEndReplay.frame W T C st'.1, st'.2), vv)
    (read_sreg_indirect reg racc (VMTransEndReplay.frame W T C ts, iis)).
Proof.
  unfold read_sreg_indirect. intro H. VMViews.invert.
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]; cbn [snd].
  all: match goal with H : dmap_lookup _ _ = _ |- _ => rewrite H end.
  all: repeat match goal with H : ?a = ?b |- _ => is_var a; is_var b; subst a end.
  all: cbn [fst snd]; try apply Exec.elem_of_mret.
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]; cbn [fst].
  all: change (TState.read_sreg_indirect (VMTransEndReplay.frame W T C ts) reg) with
    (TState.read_sreg_indirect ts reg);
    match goal with H : TState.read_sreg_indirect _ _ = Some _ |- _ => rewrite H end; cbn [othrow].
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
  all: eapply Exec.elem_of_bind_intro; [eapply Exec.elem_of_mchoosel; eassumption|].
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
  all: apply Exec.elem_of_mret.
Qed.

Section StepOwn.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

Lemma step_start_own (HB : LookupBi tid imem mem ev true) (Hown : Ev.tid ev = tid) s p p' r q0 :
  VMViews.ok p → VMCreatingReplay.ExactOwn tid imem mem ev p q0 →
  LookupShaped tid imem mem (PPState.state p) →
  Exec.elem_of_results (p', r) (run_outcome n tid imem (TranslationStart s) p) →
  ∃ q0' v rr, Exec.elem_of_results (q0', r) (run_outcome n tid imem (TranslationStart s) q0) ∧
    is_ttbr rr ∧ VMCreatingReplay.ExactOwn tid imem mem ev p' v ∧ SR rr 0 v q0'.
Proof.
  intros Hok Hex Hsh Hrun. destruct p as [ts m iis].
  destruct Hex as [Hm [issued [He ->]]].
  cbn [PPState.mem PPState.state PPState.iis] in Hm, He, Hsh. subst m.
  destruct Hok as [Hts _]. cbn [PPState.mem PPState.state] in Hts.
  simp run_outcome in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [[] [Hstart Hret]]].
  apply Exec.elem_of_mret_inv in Hret as [-> ->].
  apply ts_elim in Hstart as (Hreg & Hg & tres & inv & iis1 & Hout & Htc & ->).
  pose proof (VMBoundsReplay.emit_own_promise_min tid imem mem ev ts issued Hown He) as Hmin.
  pose proof (VMTransEndReplay.emit_promise_frame _ _ _ _ _ _ He) as Hframe.
  set (W := TState.prom_wr issued) in Hframe; set (T := TState.prom_tlbi issued) in Hframe;
    set (C := TState.tlb issued) in Hframe; clearbody W T C; subst issued.
  set (F := VMTransEndReplay.frame W T C) in *.
  assert (Hets : TState.ets2 (F ts) = TState.ets2 ts)
    by exact (proj1 (VMCacheConfig.emit_promise_ets _ _ _ _ _ _ He)).
  assert (Hvpre : ts_vpre s (F ts) iis = ts_vpre s ts iis)
    by (unfold ts_vpre; rewrite Hets; reflexivity).
  assert (Hvinv : ts_vinv s (F ts) iis = ts_vinv s ts iis)
    by (unfold ts_vinv; rewrite Hvpre, Hets; reflexivity).
  assert (Hvmax : ts_vmax (ev :: mem) (F ts) = ts_vmax mem ts)
    by (unfold ts_vmax; cbn [length]; rewrite Hmin; reflexivity).
  set (A := TranslationStartInfo_asid s) in *. set (O := ts_offs s) in *.
  assert (Hemit : ∀ v, TState.emit_promise tid imem (ev :: mem) ev (TState.update_tcohs A O v ts) =
      Ok (F (TState.update_tcohs A O v ts))) by (intro; apply emit_tcohs; exact He).
  pose proof (tcoh_bound _ _ A O Hts) as Htb.
  destruct Hout as [(Hnone & -> & -> & ->)|(upper & reg_ttbr & ttbr0 & vw & res & val_ttbr & Hup &
    Hroot & Hread & Hasid & Hres & Hval & -> & ->)].
  - set (tres' := IIS.TransRes.make (ts_vpre s (F ts) iis) (ts_vmax (ev :: mem) (F ts)) None []).
    exists (PPState.Make (TState.update_tcohs A O (IIS.TransRes.trans_start tres') (F ts)) (ev :: mem)
      (IIS.set_inv_time None (IIS.set_trs tres' iis))).
    exists (PPState.Make (F (TState.update_tcohs A O (ts_vpre s ts iis) ts)) (ev :: mem)
      (IIS.set_inv_time None (IIS.set_trs
          (IIS.TransRes.make (ts_vpre s ts iis) (ts_vmax mem ts) None []) iis))).
    exists TTBR0_EL1.
    split; [|split; [left; reflexivity|split]].
    + simp run_outcome. eapply Exec.elem_of_bind_intro; [|apply Exec.elem_of_mret].
      apply ts_intro; [exact Hreg| |left; split; [exact Hnone|split; [reflexivity|split; reflexivity]]
        |exact Logic.I].
      rewrite Hvpre, Hvmax. exact Hg.
    + split; [reflexivity|]. eexists. split; [apply Hemit|reflexivity].
    + eexists _, tres'. split; [reflexivity|]. split.
      * split; [cbn; rewrite Hvpre; reflexivity|]. split; [cbn; rewrite Hvmax; reflexivity|].
        split; [left; split; reflexivity|exact Logic.I].
      * unfold tres'. cbn [IIS.TransRes.trans_start]. rewrite Hvpre.
        apply f_equal3; [apply frame_tcohs|reflexivity|]. destruct iis; reflexivity.
  - assert (Hunc := unc_le s ts iis).
    destruct (merged_bi tid imem mem ev true HB ts (F ts) _ _ _ _ _ _ _ res Hts
      (λ _, Hown) He Hg Hunc Hres) as (res' & Hres' & Hst & Hti & Hlast & Hattr).
    pose proof (root_ttbr_is _ _ _ Hroot) as Hrr.
    destruct (val_ttbr_some reg_ttbr (TLB.Result.ttbr res') Hrr) as [val' Hval'].
    set (tres' := IIS.TransRes.make (TLB.Result.tstart res') (TLB.Result.tend res')
      (Some (existT reg_ttbr val')) (TLB.Result.path res')).
    unfold ti in Hti. cbn in Hti.
    pose proof (f_equal fst Hti) as Hend. pose proof (f_equal snd Hti) as Hinv. cbn in Hend, Hinv.
    exists (PPState.Make (TState.update_tcohs A O (IIS.TransRes.trans_start tres') (F ts)) (ev :: mem)
      (IIS.set_inv_time (TLB.Result.inv_time res') (IIS.set_trs tres' iis1))).
    exists (PPState.Make (F (TState.update_tcohs A O (TLB.Result.tstart res) ts)) (ev :: mem)
        (IIS.set_inv_time (TLB.Result.inv_time res) (IIS.set_trs
          (IIS.TransRes.make (TLB.Result.tstart res) (TLB.Result.tend res)
            (Some (existT reg_ttbr val_ttbr)) (TLB.Result.path res)) iis1))).
    exists reg_ttbr.
    split; [|split; [exact Hrr|split]].
    + simp run_outcome. eapply Exec.elem_of_bind_intro; [|apply Exec.elem_of_mret].
      apply ts_intro; [exact Hreg| | |].
      * rewrite Hvpre, Hvmax. exact Hg.
      * right. exists upper, reg_ttbr, ttbr0, vw, res', val'.
        split; [exact Hup|]. split; [exact Hroot|].
        split; [exact (indirect_frame W T C TTBR0_EL1 None ts iis _ _ Hread)|].
        split; [exact Hasid|]. split; [rewrite Hvpre, Hvinv; exact Hres'|].
        split; [exact Hval'|]. split; reflexivity.
      * rewrite <- Hinv.
        exact (VMTransEndReplay.tcohs_after_promise tid imem mem ev ts (F ts) A O
          (TLB.Result.inv_time res) (TLB.Result.inv_time res) He Htb (or_introl eq_refl) Htc).
    + split; [reflexivity|]. eexists. split; [apply Hemit|reflexivity].
    + eexists _, tres'. split; [reflexivity|]. split.
      * split; [cbn; symmetry; exact Hst|]. split; [cbn; exact Hend|].
        split; [right; eexists _, _; split; reflexivity|].
        cbn [IIS.TransRes.remaining tres'].
        apply prel_of_key; [|symmetry; exact Hlast|symmetry; exact Hattr].
        destruct (merge_src _ _ Hres) as (y & Hy & Hp). rewrite Hp. eapply Hsh. exact Hy.
      * unfold tres'. cbn [IIS.TransRes.trans_start]. rewrite Hst, <- Hinv.
        apply f_equal3; [apply frame_tcohs|reflexivity|]. destruct iis1; reflexivity.
Qed.
End StepOwn.

(** * The translation-start obligations *)

Local Notation ppstate := (PPState.t TState.t Ev.t IIS.t).

(** The walk-shape invariant of an original state. *)
Definition Shape {n} (tid : fin n) (imem : memoryMap) (p : ppstate) : Prop :=
  LookupShaped tid imem (PPState.mem p) (PPState.state p).

Theorem step_start_w {n} (tid : fin n) imem mem ev :
  LookupBi tid imem mem ev false → StepStartW tid imem mem ev (Shape tid imem).
Proof.
  intros HB s p p' r q0 Hok _ HSh Hex _ _ Hrun.
  assert (Hm : PPState.mem p = mem) by exact (proj1 Hex).
  unfold Shape in HSh. rewrite Hm in HSh.
  exact (step_start_f tid imem mem ev HB s p p' r q0 Hok Hex HSh Hrun).
Qed.

Theorem step_start_own_w {n} (tid : fin n) imem mem ev :
  LookupBi tid imem mem ev true → Ev.tid ev = (tid : nat) →
  StepStartOwnW tid imem mem ev (Shape tid imem).
Proof.
  intros HB Hown s p p' r q0 Hok _ HSh Hex _ _ Hrun.
  assert (Hm : PPState.mem p = mem) by exact (proj1 Hex).
  unfold Shape in HSh. rewrite Hm in HSh.
  exact (step_start_own tid imem mem ev HB Hown s p p' r q0 Hok Hex HSh Hrun).
Qed.

Section Final.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n)
  (initMs : archState n) (code : code_region).

(** The lookup-level replay for events with positive-sized writes. Sail fresh
    events and certification candidates satisfy this restriction. *)
Definition LookupReplay : Prop :=
  ∀ (tid : fin n) imem mem ev own, VMEventValidity.event_positive ev →
    LookupBi tid imem mem ev own.

Corollary start_replay : LookupReplay → StartReplay (@Shape n).
Proof. intros HL tid imem mem ev Hpositive. apply step_start_w, HL, Hpositive. Qed.

Corollary start_own_replay : LookupReplay → StartOwnReplayW (@Shape n).
Proof.
  intros HL tid imem mem ev Hpositive Hown.
  apply step_start_own_w; [apply HL, Hpositive|exact Hown].
Qed.

(** The final-state equivalence with both translation-start obligations
    discharged: what remains is the lookup-level replay, the walk-shape
    invariant, the TLBI exchange, code immutability and search
    completeness. *)
Theorem final_state_equiv_start :
  LookupReplay → ShInvariant bbm nondet term initMs (@Shape n) →
  VMNormalization.VMTLBISwapReplay bbm nondet term initMs code →
  VMSailNoSelfModifying bbm nondet term initMs code →
  (∀ initPs fuel returned fsig,
    PState.from_archState (VMPromising bbm) initMs = Ok initPs →
    Exec.elem_of_results (returned, fsig)
      (opModel.run (@CPState.opmodel (sail_tiny_arm_sem nondet) (VMPromising bbm) n)
        fuel term initMs initPs) →
    VMNormalization.VMNormalizationSearchesComplete bbm nondet term initMs (projT1 fsig)) →
  (∀ fuel fs (pt : archState.is_terminated term fs),
    archModel.Res.FinalState fs pt ∈
      Promising_to_Modelc_pf_uncached (VMPromising bbm) (sail_tiny_arm_sem nondet)
        fuel n term initMs →
    PromiseFirstSearchesCompleteFromInitial (VMPromising bbm) nondet term initMs fuel) →
  VMPromisingFinalStateEquiv bbm (sail_tiny_arm_sem nondet) term initMs.
Proof.
  intros HL HSh.
  apply (final_state_equiv_walks bbm nondet term initMs code (@Shape n) HSh).
  - apply start_replay, HL.
  - apply start_own_replay, HL.
Qed.
End Final.
End VMWalkStart.
