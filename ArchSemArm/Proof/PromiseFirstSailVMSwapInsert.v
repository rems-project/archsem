(******************************************************************************)
(* Outcome handlers over a history with an inserted TLBI                      *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstFreshBroadcast
  PromiseFirstSailSerialization PromiseFirstSailVMNormalization
  PromiseFirstSailVMCacheSim PromiseFirstSailVMCacheState
  PromiseFirstSailVMViews PromiseFirstSailVMSwapSim PromiseFirstSailVMSwapLookup
  PromiseFirstSailVMSwapPos.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

(** The insertion direction of the exchange simulation for a thread [tid]
    that is not the recipient of the inserted TLBI [Ev.Tlbi tlbi rc k]. The
    shorter history is [l ++ r], the longer one [l ++ Ev.Tlbi tlbi rc k :: r];
    new events are added in front of both, so [r] and [p = S (length r)] stay
    fixed. Thread states are related by [ts_map (shift p)], instruction
    states by [iis_rel p]. The handlers are related by [esim] of
    VMCacheSimOutcome: every result and every error state of the shorter run
    has a counterpart of the longer run. *)

Module VMSwapInsert.
Import VMPromising VMSwapSim VMSwapLookup VMSwapPos VMCacheSimOutcome.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

(** * Thread-state operations under a time map *)

Section Map.
Context (p : nat) (Hp : 0 < p).
Set Default Proof Using "All".
Local Notation f := (shift p).

Ltac map_fields :=
  match goal with ts : TState.t |- _ => destruct ts end;
  unfold TState.update, TState.set_xclb, TState.clear_xclb, TState.promise_write,
    TState.promise_tlbi, setv, set, ts_map;
  cbn -[shift regs_map dmap_map fmap map lev_map tlb_map fwd_map xcl_map];
  rewrite ?shift_max; reflexivity.

Local Notation upd acc :=
  (∀ v ts, ts_map f (TState.update acc v ts) = TState.update acc (f v) (ts_map f ts)).
Lemma map_vrd : upd TState.vrd. Proof. intros. map_fields. Qed.
Lemma map_vwr : upd TState.vwr. Proof. intros. map_fields. Qed.
Lemma map_vdmbst : upd TState.vdmbst. Proof. intros. map_fields. Qed.
Lemma map_vdmb : upd TState.vdmb. Proof. intros. map_fields. Qed.
Lemma map_vdsb : upd TState.vdsb. Proof. intros. map_fields. Qed.
Lemma map_vspec : upd TState.vspec. Proof. intros. map_fields. Qed.
Lemma map_vcse : upd TState.vcse. Proof. intros. map_fields. Qed.
Lemma map_vtlbi_self : upd TState.vtlbi_self. Proof. intros. map_fields. Qed.
Lemma map_vtlbi_other : upd TState.vtlbi_other. Proof. intros. map_fields. Qed.
Lemma map_vmsr : upd TState.vmsr. Proof. intros. map_fields. Qed.
Lemma map_vacq : upd TState.vacq. Proof. intros. map_fields. Qed.
Lemma map_vrel : upd TState.vrel. Proof. intros. map_fields. Qed.

Lemma map_set_xclb time a size v ts :
  ts_map f (TState.set_xclb time a size v ts) =
  TState.set_xclb (f time) a size (f v) (ts_map f ts).
Proof. map_fields. Qed.

Lemma map_clear_xclb ts : ts_map f (TState.clear_xclb ts) = TState.clear_xclb (ts_map f ts).
Proof. map_fields. Qed.

Lemma map_promise_write v ts :
  ts_map f (TState.promise_write v ts) = TState.promise_write (f v) (ts_map f ts).
Proof. map_fields. Qed.

Lemma map_promise_tlbi v ts :
  ts_map f (TState.promise_tlbi v ts) = TState.promise_tlbi (f v) (ts_map f ts).
Proof. map_fields. Qed.

Lemma map_next_epoch ts : ts_map f (set TState.dsb_epoch S ts) = set TState.dsb_epoch S (ts_map f ts).
Proof. map_fields. Qed.

Lemma filter_map_ne (l : list nat) t :
  filter (λ x, x ≠ f t) (map f l) = map f (filter (λ x, x ≠ t) l).
Proof.
  induction l as [|x l IH]; [reflexivity|]. cbn [map]. rewrite !filter_cons.
  pose proof (shift_inj p x t). repeat case_decide;
    first [exact IH|cbn; rewrite IH; reflexivity|exfalso; naive_solver].
Qed.

Lemma map_filter_prom_wr t ts :
  ts_map f (set TState.prom_wr (filter (λ x, x ≠ t)) ts) =
  set TState.prom_wr (filter (λ x, x ≠ f t)) (ts_map f ts).
Proof.
  destruct ts. unfold set, ts_map. cbn -[shift regs_map dmap_map fmap map lev_map tlb_map fwd_map xcl_map filter].
  rewrite filter_map_ne. reflexivity.
Qed.

Lemma map_filter_prom_tlbi t ts :
  ts_map f (set TState.prom_tlbi (filter (λ x, x ≠ t)) ts) =
  set TState.prom_tlbi (filter (λ x, x ≠ f t)) (ts_map f ts).
Proof.
  destruct ts. unfold set, ts_map. cbn -[shift regs_map dmap_map fmap map lev_map tlb_map fwd_map xcl_map filter].
  rewrite filter_map_ne. reflexivity.
Qed.

Lemma lookup_total_map {K} `{Countable K} (m : gmap K nat) a : (f <$> m) !!! a = f (m !!! a).
Proof using Hp.
  rewrite !lookup_total_alt, lookup_fmap. destruct (m !! a); cbn; [reflexivity|].
  symmetry. apply shift_zero, Hp.
Qed.

Lemma map_update_cohs avs ts :
  ts_map f (TState.update_cohs avs ts) =
  TState.update_cohs (map (λ av, (av.1, f av.2)) avs) (ts_map f ts).
Proof using Hp.
  induction avs as [|[a v] avs IH]; [reflexivity|]. cbn [map foldr TState.update_cohs fst snd].
  change (ts_map f (TState.update_coh a v (TState.update_cohs avs ts)) =
    TState.update_coh a (f v) (TState.update_cohs (map (λ av, (av.1, f av.2)) avs) (ts_map f ts))).
  rewrite <- IH. generalize (TState.update_cohs avs ts). intro t.
  unfold TState.update_coh, TState.set_coh.
  replace (TState.coh (ts_map f t)) with (f <$> TState.coh t) by (destruct t; reflexivity).
  rewrite lookup_total_map, <- shift_max.
  destruct t. unfold set, ts_map. cbn -[shift regs_map dmap_map fmap map lev_map tlb_map fwd_map xcl_map].
  rewrite fmap_insert. reflexivity.
Qed.

Lemma map_update_tcohs asid offs v ts :
  ts_map f (TState.update_tcohs asid offs v ts) = TState.update_tcohs asid offs (f v) (ts_map f ts).
Proof using Hp.
  induction offs as [|o offs IH]; [reflexivity|]. cbn [foldr].
  change (ts_map f (TState.update_tcoh asid o v (TState.update_tcohs asid offs v ts)) =
    TState.update_tcoh asid o (f v) (TState.update_tcohs asid offs (f v) (ts_map f ts))).
  rewrite <- IH. generalize (TState.update_tcohs asid offs v ts). intro t.
  destruct t. unfold TState.update_tcoh, set, ts_map.
  cbn -[shift regs_map dmap_map fmap map lev_map tlb_map fwd_map xcl_map partial_alter].
  f_equal. apply map_eq. intro key. rewrite lookup_fmap.
  destruct (decide (key = (asid, o))) as [->|Hne].
  - rewrite !lookup_partial_alter, lookup_fmap.
    rewrite !decide_True by reflexivity.
    cbn [fmap option_fmap option_map]. f_equal.
    assert (Hd : ∀ o0 : option nat, f (v `max` default 0 o0) = f v `max` default 0 (f <$> o0))
      by (intros [x|]; cbn; shift_cases).
    apply Hd.
  - rewrite !lookup_partial_alter_ne by congruence. rewrite lookup_fmap. reflexivity.
Qed.

Lemma map_set_fwdbs addrs n (data : bv n) time vdata xcl ts :
  ts_map f (TState.set_fwdbs addrs data time vdata xcl ts) =
  TState.set_fwdbs addrs data (f time) (f vdata) (f <$> xcl) (ts_map f ts).
Proof.
  unfold TState.set_fwdbs. generalize (zip addrs (bv_to_bytes 8 data)). intro l.
  revert ts. induction l as [|[a b] l IH]; intro ts; [reflexivity|]. cbn [foldl].
  rewrite IH. f_equal. destruct ts. unfold TState.set_fwdb, set, ts_map.
  cbn -[shift regs_map dmap_map fmap map lev_map tlb_map xcl_map].
  rewrite fmap_insert. reflexivity.
Qed.

Lemma map_set_reg reg vv ts :
  TState.set_reg reg (vv_map f vv) (ts_map f ts) = ts_map f <$> TState.set_reg reg vv ts.
Proof.
  unfold TState.set_reg. cbn [ts_map TState.regs]. unfold regs_map.
  rewrite dmap_lookup_map.
  destruct (dmap_lookup reg (TState.regs ts)) eqn:E; rewrite ?E; cbn.
  - rewrite !decide_True by auto. cbn. f_equal.
    destruct ts. unfold set, ts_map. cbn -[shift dmap_map fmap map lev_map tlb_map fwd_map xcl_map].
    f_equal. unfold regs_map. apply dmap_eq. intro key.
    rewrite dmap_lookup_map. destruct (decide (key = reg)) as [->|Hne].
    + rewrite !dmap_lookup_insert. reflexivity.
    + rewrite !dmap_lookup_insert_ne by congruence. rewrite dmap_lookup_map. reflexivity.
  - rewrite !decide_False by (intros [? H]; discriminate). reflexivity.
Qed.

Lemma map_read_reg ts reg :
  TState.read_reg (ts_map f ts) reg = vv_map f <$> TState.read_reg ts reg.
Proof.
  unfold TState.read_reg. case_bool_decide; [apply ts_map_read_sreg_direct|].
  cbn [ts_map TState.regs]. unfold regs_map. rewrite dmap_lookup_map.
  destruct (dmap_lookup reg (TState.regs ts)) eqn:E; rewrite ?E; reflexivity.
Qed.

(** ** Guards *)

Lemma map_no_promises_until v ts :
  TState.no_promises_until (f v) (ts_map f ts) ↔ TState.no_promises_until v ts.
Proof.
  unfold TState.no_promises_until. cbn [ts_map TState.prom_wr TState.prom_tlbi].
  rewrite <- map_app. split; intros H q Hq.
  - apply (proj1 (shift_lt_iff p _ _)), H, list_elem_of_fmap. eauto.
  - apply list_elem_of_fmap in Hq as [q0 [-> Hq0]]. apply (proj2 (shift_lt_iff p _ _)), H, Hq0.
Qed.

Lemma map_no_write_promises_until v ts :
  TState.no_write_promises_until (f v) (ts_map f ts) ↔ TState.no_write_promises_until v ts.
Proof.
  unfold TState.no_write_promises_until. cbn [ts_map TState.prom_wr]. split; intros H q Hq.
  - apply (proj1 (shift_lt_iff p _ _)), H, list_elem_of_fmap. eauto.
  - apply list_elem_of_fmap in Hq as [q0 [-> Hq0]]. apply (proj2 (shift_lt_iff p _ _)), H, Hq0.
Qed.

Lemma foldr_min_map base base' (l : list nat) : base' = f base →
  foldr (λ q v, v `min` q) base' (map f l) = f (foldr (λ q v, v `min` q) base l).
Proof.
  intros ->. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite IH. shift_cases.
Qed.

(** The bound of [min_promise] is the memory length, which grows by one. *)
Lemma map_min_promise vmax vmax' ts : S vmax' = f (S vmax) →
  TState.min_promise vmax' (ts_map f ts) = f (TState.min_promise vmax ts).
Proof.
  intro H. unfold TState.min_promise. cbn [ts_map TState.prom_wr TState.prom_tlbi].
  rewrite <- map_app. apply foldr_min_map. rewrite !Nat.add_1_r. exact H.
Qed.

Lemma foldl_min_map (m : gmap address nat) addrs x :
  foldl (λ res addr, res `min` (f <$> m) !!! addr) (f x) addrs =
  f (foldl (λ res addr, res `min` m !!! addr) x addrs).
Proof.
  revert x. induction addrs as [|b addrs IH]; intro x; [reflexivity|]. cbn [foldl].
  rewrite lookup_total_map.
  replace (f x `min` f (m !!! b)) with (f (x `min` m !!! b)) by shift_cases.
  apply IH.
Qed.

Lemma map_min_cohs addrs ts : TState.min_cohs addrs (ts_map f ts) = f (TState.min_cohs addrs ts).
Proof using Hp.
  unfold TState.min_cohs. destruct addrs as [|a addrs]; [symmetry; apply shift_zero, Hp|].
  replace (TState.coh (ts_map f ts)) with (f <$> TState.coh ts) by (destruct ts; reflexivity).
  rewrite lookup_total_map. apply foldl_min_map.
Qed.

Lemma map_ets2 ts : TState.ets2 (ts_map f ts) = TState.ets2 ts.
Proof. unfold TState.ets2. cbn [ts_map TState.tlb]. destruct (TState.tlb ts); reflexivity. Qed.

Lemma map_ets3 ts : TState.ets3 (ts_map f ts) = TState.ets3 ts.
Proof. unfold TState.ets3. cbn [ts_map TState.tlb]. destruct (TState.tlb ts); reflexivity. Qed.

Lemma map_xclb ts : TState.xclb (ts_map f ts) = xcl_map f <$> TState.xclb ts.
Proof. reflexivity. Qed.

Lemma map_dsb_epoch ts : TState.dsb_epoch (ts_map f ts) = TState.dsb_epoch ts.
Proof. reflexivity. Qed.

Lemma shift_view_if b x : view_if b (f x) = f (view_if b x).
Proof using Hp. unfold view_if, UMPromising.view_if. destruct b; [reflexivity|]. symmetry. apply shift_zero, Hp. Qed.

Lemma shift_le_unshift t te' : f t ≤ te' ↔ t ≤ unshift p te'.
Proof. shift_cases. Qed.

Lemma leb_shift a b' : (f a <=? b') = (a <=? unshift p b').
Proof.
  pose proof (shift_le_unshift a b').
  destruct (Nat.leb_spec (f a) b'), (Nat.leb_spec a (unshift p b')); tauto || lia.
Qed.

(** ** Instruction states *)

Lemma iis_rel_add v i1 i2 : iis_rel p i1 i2 → iis_rel p (IIS.add v i1) (IIS.add (f v) i2).
Proof.
  intros (Hs & Ht & Hi & Hr & Hsr). destruct i1, i2; cbn in *.
  unfold IIS.add, set. cbn. repeat split; try assumption. rewrite Hs, shift_max. reflexivity.
Qed.

Lemma iis_rel_set_trs t1 t2 i1 i2 : iis_rel p i1 i2 → trs_rel p t1 t2 →
  iis_rel p (IIS.set_trs t1 i1) (IIS.set_trs t2 i2).
Proof. intros (Hs & Ht & Hi & Hr & Hsr) H. destruct i1, i2; cbn in *. refine (conj _ (conj _ (conj _ (conj _ _)))); cbn; first [assumption|exact I|reflexivity]. Qed.

Lemma iis_rel_clear_trs i1 i2 : iis_rel p i1 i2 →
  iis_rel p (setv IIS.trs None i1) (setv IIS.trs None i2).
Proof. intros (Hs & Ht & Hi & Hr & Hsr). destruct i1, i2; cbn in *. refine (conj _ (conj _ (conj _ (conj _ _)))); cbn; first [assumption|exact I|reflexivity]. Qed.

Lemma iis_rel_set_some_trs t1 t2 i1 i2 : iis_rel p i1 i2 → trs_rel p t1 t2 →
  iis_rel p (setv IIS.trs (Some t1) i1) (setv IIS.trs (Some t2) i2).
Proof. intros (Hs & Ht & Hi & Hr & Hsr) H. destruct i1, i2; cbn in *. refine (conj _ (conj _ (conj _ (conj _ _)))); cbn; first [assumption|exact I|reflexivity]. Qed.

Lemma iis_rel_set_inv_time o i1 i2 : iis_rel p i1 i2 →
  iis_rel p (IIS.set_inv_time o i1) (IIS.set_inv_time (f <$> o) i2).
Proof. intros (Hs & Ht & Hi & Hr & Hsr). destruct i1, i2; cbn in *. refine (conj _ (conj _ (conj _ (conj _ _)))); cbn; first [assumption|exact I|reflexivity]. Qed.

Lemma iis_rel_set_rmw o i1 i2 : iis_rel p i1 i2 →
  iis_rel p (setv IIS.rmw_read o i1)
    (setv IIS.rmw_read ((λ tb : nat * bool, (f tb.1, tb.2)) <$> o) i2).
Proof. intros (Hs & Ht & Hi & Hr & Hsr). destruct i1, i2; cbn in *. refine (conj _ (conj _ (conj _ (conj _ _)))); cbn; first [assumption|exact I|reflexivity]. Qed.

Lemma regs_map_insert reg vv m :
  regs_map f (dmap_insert reg vv m) = dmap_insert reg (vv_map f vv) (regs_map f m).
Proof.
  unfold regs_map. apply dmap_eq. intro key. rewrite dmap_lookup_map.
  destruct (decide (key = reg)) as [->|Hne].
  - rewrite !dmap_lookup_insert. reflexivity.
  - rewrite !dmap_lookup_insert_ne by congruence. rewrite dmap_lookup_map. reflexivity.
Qed.

Lemma iis_rel_add_sreg_read reg vv i1 i2 : iis_rel p i1 i2 →
  iis_rel p (IIS.add_sreg_read reg vv i1) (IIS.add_sreg_read reg (vv_map f vv) i2).
Proof.
  intros (Hs & Ht & Hi & Hr & Hsr). destruct i1, i2; cbn in *.
  unfold IIS.add_sreg_read, set. cbn. repeat split; try assumption.
  rewrite Hsr, regs_map_insert. reflexivity.
Qed.

Lemma pop_rel t1 t2 : trs_rel p t1 t2 →
  match IIS.TransRes.pop t1, IIS.TransRes.pop t2 with
  | Ok (t1', v1), Ok (t2', v2) => trs_rel p t1' t2' ∧ v1 = v2
  | Error _, Error _ => True
  | _, _ => False
  end.
Proof.
  intros (Hs & He & Hr & Hm). unfold IIS.TransRes.pop. rewrite Hm.
  destruct (IIS.TransRes.remaining t1) as [|h tl]; [exact I|]. cbn.
  destruct t1, t2; cbn in *.
  refine (conj (conj _ (conj _ (conj _ _))) _); cbn; first [assumption|reflexivity].
Qed.

End Map.

(** * Relational handlers *)

Section Handlers.
Context (r : Memory.t) (tlbi : TLBI.t) (rc k : nat) (n_threads tid : nat) (imem : memoryMap).
Local Notation p := (S (length r)).
Local Notation f := (shift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc k).
Set Default Proof Using "Type".

Lemma Hp : 0 < p.
Proof. apply Nat.lt_0_succ. Qed.

Definition mem_rel (m m' : Memory.t) := ∃ l, m = l ++ r ∧ m' = l ++ e :: r.

Definition pp_rel (a b : PPState.t TState.t Ev.t IIS.t) :=
  mem_rel (PPState.mem a) (PPState.mem b) ∧ PPState.state b = ts_map f (PPState.state a) ∧
  iis_rel p (PPState.iis a) (PPState.iis b) ∧ ts_pos (PPState.state a).

Definition pr_rel (a b : TState.t * IIS.t) :=
  b.1 = ts_map f a.1 ∧ iis_rel p a.2 b.2 ∧ ts_pos a.1.

Definition tsr (a b : TState.t) := b = ts_map f a ∧ ts_pos a.

Definition vr (v v' : nat) := v' = f v.

Lemma mem_rel_length m m' : mem_rel m m' → length m' = S (length m).
Proof. intros (l & -> & ->). rewrite insert_length. reflexivity. Qed.

Lemma mem_rel_length_le m m' : mem_rel m m' → f (length m) ≤ length m'.
Proof. intro H. rewrite (mem_rel_length _ _ H). shift_cases. Qed.

Ltac bind V := eapply (esim_bind _ V); [|
  let x := fresh "x" in let y := fresh "y" in let H := fresh "Hxy" in intros x y H;
  lazymatch type of x with unit => clear H; destruct x, y | _ => idtac end].

Ltac gbind tac := eapply esim_bind;
  [apply esim_guard_discard; let HG := fresh "HG" in intro HG; tac; exact HG|intros ? ? _].

Ltac fold_shift :=
  unfold join, join_nat in *;
  repeat first [rewrite (shift_view_if _ Hp)|rewrite <- shift_max].

Lemma esim_get_state : esim pp_rel tsr (mget PPState.state) (mget PPState.state).
Proof. apply esim_mget. intros s1 s2 (_ & H & _ & Hq). split; assumption. Qed.

Lemma esim_get_iis : esim pp_rel (iis_rel p) (mget PPState.iis) (mget PPState.iis).
Proof. apply esim_mget. intros s1 s2 (_ & _ & H & _). exact H. Qed.

Lemma esim_get_mem : esim pp_rel mem_rel (mget PPState.mem) (mget PPState.mem).
Proof. apply esim_mget. intros s1 s2 (H & _). exact H. Qed.

Lemma esim_get_strict :
  esim pp_rel vr (mget (IIS.strict ∘ PPState.iis)) (mget (IIS.strict ∘ PPState.iis)).
Proof. apply esim_mget. intros s1 s2 (_ & _ & H & _). apply H. Qed.

Lemma esim_set_state (g1 g2 : TState.t → TState.t) :
  (∀ ts, g2 (ts_map f ts) = ts_map f (g1 ts)) → (∀ ts, TState.tlb (g1 ts) = TState.tlb ts) →
  esim pp_rel eq (mset PPState.state g1) (mset PPState.state g2).
Proof.
  intros Hg Ht. apply esim_mset. intros [a1 m1 i1] [a2 m2 i2] (Hm & Ha & Hi & Hq).
  cbn in *. subst a2. split; [exact Hm|]. split; [apply Hg|]. split; [exact Hi|].
  eapply ts_pos_eq; [apply Ht|exact Hq].
Qed.

Lemma esim_setv_state t1 t2 : tsr t1 t2 → esim pp_rel eq (msetv PPState.state t1) (msetv PPState.state t2).
Proof.
  intros [-> Hq]. apply esim_mset. intros [a1 m1 i1] [a2 m2 i2] (Hm & Ha & Hi & _).
  cbn in *. refine (conj _ (conj _ (conj _ _))); cbn; first [assumption|reflexivity].
Qed.

Lemma esim_set_iis (g1 g2 : IIS.t → IIS.t) :
  (∀ i1 i2, iis_rel p i1 i2 → iis_rel p (g1 i1) (g2 i2)) →
  esim pp_rel eq (mset PPState.iis g1) (mset PPState.iis g2).
Proof.
  intros Hg. apply esim_mset. intros [a1 m1 i1] [a2 m2 i2] (Hm & Ha & Hi & Hq).
  cbn in *. refine (conj _ (conj _ (conj _ _))); cbn; first [assumption|apply Hg, Hi].
Qed.

Lemma esim_add v v' : vr v v' → esim pp_rel eq (mset PPState.iis (IIS.add v)) (mset PPState.iis (IIS.add v')).
Proof. intros ->. apply esim_set_iis. intros. apply iis_rel_add; [exact Hp|assumption]. Qed.

(** ** Barriers and context synchronization *)

Lemma cse_candidates_map vpre vmax vmax' ts v : f vmax ≤ vmax' →
  v ∈ TState.cse_candidates vpre vmax ts →
  f v ∈ TState.cse_candidates (f vpre) vmax' (ts_map f ts).
Proof.
  intros Hmax Hin. unfold TState.cse_candidates in *. apply elem_of_seq in Hin. apply elem_of_seq.
  set (L := TState.prom_wr ts ++ TState.prom_tlbi ts).
  assert (Hm : TState.min_promise vmax' (ts_map f ts) = foldr (λ q w, w `min` q) (vmax' + 1) (map f L)).
  { unfold TState.min_promise, L. cbn [ts_map TState.prom_wr TState.prom_tlbi]. rewrite map_app.
    reflexivity. }
  assert (Hm0 : TState.min_promise vmax ts = foldr (λ q w, w `min` q) (vmax + 1) L) by reflexivity.
  rewrite Hm. rewrite Hm0 in Hin.
  assert (Hlt : ∀ (l : list nat) b b', v < foldr (λ q w, w `min` q) b l → f v < b' →
    f v < foldr (λ q w, w `min` q) b' (map f l)).
  { induction l as [|x l IH]; intros b b' H1 H2; cbn in *; [exact H2|].
    apply Nat.min_glb_lt; [apply (IH b b'); [lia|exact H2]|apply (proj2 (shift_lt_iff p _ _)); lia]. }
  assert (Hb : ∀ l b, foldr (λ q w, w `min` q) b l ≤ b) by (intros l0 b; induction l0; cbn; lia).
  pose proof (Hb L (vmax + 1)). pose proof (proj2 (shift_le_iff p vpre v) ltac:(lia)).
  pose proof (proj2 (shift_le_iff p v vmax) ltac:(lia)).
  assert (f v < foldr (λ q w, w `min` q) (vmax' + 1) (map f L)) by (apply (Hlt L (vmax + 1)); lia).
  lia.
Qed.

Lemma run_cse_sim (Hrc : tid ≠ rc) vmax vmax' : f vmax ≤ vmax' →
  esim pp_rel eq (run_cse tid imem vmax) (run_cse tid imem vmax').
Proof.
  intro Hmax. unfold run_cse.
  bind tsr; [apply esim_get_state|]. destruct Hxy as [-> Hq].
  bind mem_rel; [apply esim_get_mem|].
  bind (iis_rel p); [apply esim_get_iis|].
  destruct Hxy0 as (Hs & _). rewrite Hs. cbn [ts_map TState.vspec TState.vcse TState.vdsb TState.vmsr].
  fold_shift.
  gbind ltac:(apply (map_no_promises_until _ Hp)).
  bind vr.
  { split; [|apply eerr_nil; reflexivity].
    intros s1 s2 s1' v Hs1 Hin. apply Exec.elem_of_mchoosel_inv in Hin as [-> Hv].
    exists s2, (f v). split; [apply Exec.elem_of_mchoosel|split; [exact Hs1|reflexivity]].
    eapply cse_candidates_map; eassumption. }
  rewrite Hxy0. destruct Hxy as (l & -> & ->).
  bind tsr.
  { apply esim_lift_result.
    - intros nts Hn. rewrite (cse_shifted tid imem l r tlbi rc k _ _ Hrc), Hn.
      eexists. split; [reflexivity|]. split; [reflexivity|]. eapply cse_pos; eassumption.
    - intros err Hn. rewrite (cse_shifted tid imem l r tlbi rc k _ _ Hrc), Hn. eauto. }
  bind (@eq unit); [apply esim_setv_state, Hxy|]. apply esim_add. reflexivity.
Qed.

Lemma run_barrier_sim (Hrc : tid ≠ rc) barrier vmax vmax' : f vmax ≤ vmax' →
  esim pp_rel eq (run_barrier tid imem barrier vmax) (run_barrier tid imem barrier vmax').
Proof.
  intro Hmax. unfold run_barrier.
  bind tsr; [apply esim_get_state|]. destruct Hxy as [-> Hq].
  destruct barrier as [b|b|[]| | | ]; try apply esim_throw; try (apply run_cse_sim; [exact Hrc|exact Hmax]).
  all: destruct (DxB_types b).
  all: try (match goal with |- context[if ?c then _ else _] => destruct c end).
  all: cbn [ts_map TState.vrd TState.vwr TState.vcse TState.vdsb TState.vdmb TState.vdmbst
        TState.vtlbi_self TState.vtlbi_other]; fold_shift.
  all: gbind ltac:(first [apply (map_no_promises_until _ Hp)|apply (map_no_write_promises_until _ Hp)]).
  all: repeat (bind (@eq unit); [apply esim_set_state; [intro; symmetry; first [apply (map_vdmb _ Hp)
    |apply (map_vdmbst _ Hp)|apply (map_vdsb _ Hp)|apply (map_next_epoch _ Hp)]|reflexivity]|]).
  all: apply esim_add; reflexivity.
Qed.

Lemma run_take_exception_sim (Hrc : tid ≠ rc) fault vmax vmax' : f vmax ≤ vmax' →
  esim pp_rel eq (run_take_exception tid imem fault vmax) (run_take_exception tid imem fault vmax').
Proof.
  intro Hmax. unfold run_take_exception.
  bind (λ o o' : option nat, o' = f <$> o).
  { apply esim_mget. intros s1 s2 (_ & _ & Hi & _). apply Hi. }
  subst y. destruct x as [t|]; cbn; apply run_cse_sim; [exact Hrc|lia|exact Hrc|exact Hmax].
Qed.

Lemma read_pte_sim : esim pp_rel eq read_pte read_pte.
Proof.
  unfold read_pte.
  bind (option_rel (trs_rel p)).
  { apply esim_mget. intros s1 s2 (_ & _ & Hi & _). apply Hi. }
  bind (trs_rel p).
  { apply esim_othrow; [intros t Ht; subst x; destruct y; [eexists; split; [reflexivity|exact Hxy]|
      contradiction]|intros ->; destruct y; [contradiction|reflexivity]]. }
  bind (λ a b : IIS.TransRes.t * bv 64, trs_rel p a.1 b.1 ∧ a.2 = b.2).
  { pose proof (pop_rel _ Hp x0 y0 Hxy0) as Hpop.
    apply esim_lift_result.
    - intros [t1 v] Ht. rewrite Ht in Hpop.
      destruct (IIS.TransRes.pop y0) as [[t2 v2]|]; [|contradiction].
      eexists. split; [reflexivity|]. exact Hpop.
    - intros err Ht. rewrite Ht in Hpop.
      destruct (IIS.TransRes.pop y0) as [[t2 v2]|]; [contradiction|eauto]. }
  destruct x1 as [t1 v1], y1 as [t2 v2], Hxy1 as [Ht Hv]. cbn in Ht, Hv. subst v2.
  bind (@eq unit); [|apply esim_ret; reflexivity].
  apply esim_mset. intros [a1 m1 i1] [a2 m2 i2] (Hm & Ha & Hi & Hq). cbn in *.
  refine (conj _ (conj _ (conj _ _))); cbn; try assumption.
  apply (iis_rel_set_some_trs _ Hp); assumption.
Qed.

(** ** Thread and instruction state pairs *)

Lemma esim_pr_fst : esim pr_rel tsr (mget fst) (mget fst).
Proof. apply esim_mget. intros s1 s2 (H & _ & Hq). split; assumption. Qed.

Lemma esim_pr_snd : esim pr_rel (iis_rel p) (mget snd) (mget snd).
Proof. apply esim_mget. intros s1 s2 (_ & H & _). exact H. Qed.

Lemma esim_pr_set_fst (g1 g2 : TState.t → TState.t) :
  (∀ ts, g2 (ts_map f ts) = ts_map f (g1 ts)) → (∀ ts, TState.tlb (g1 ts) = TState.tlb ts) →
  esim pr_rel eq (mset fst g1) (mset fst g2).
Proof.
  intros Hg Ht. apply esim_mset. intros [a1 i1] [a2 i2] (Ha & Hi & Hq). cbn in *. subst a2.
  refine (conj _ (conj _ _)); cbn; [apply Hg|exact Hi|eapply ts_pos_eq; [apply Ht|exact Hq]].
Qed.

Lemma esim_pr_set_snd (g1 g2 : IIS.t → IIS.t) :
  (∀ i1 i2, iis_rel p i1 i2 → iis_rel p (g1 i1) (g2 i2)) →
  esim pr_rel eq (mset snd g1) (mset snd g2).
Proof.
  intros Hg. apply esim_mset. intros [a1 i1] [a2 i2] (Ha & Hi & Hq). cbn in *.
  refine (conj _ (conj _ _)); cbn; [exact Ha|apply Hg, Hi|exact Hq].
Qed.

Lemma esim_pr_add v v' : vr v v' → esim pr_rel eq (mset snd (IIS.add v)) (mset snd (IIS.add v')).
Proof. intros ->. apply esim_pr_set_snd. intros. apply iis_rel_add; [exact Hp|assumption]. Qed.

Lemma esim_liftSt_pr {A B} (V : A → B → Prop) m1 m2 :
  esim pr_rel V m1 m2 →
  esim pp_rel V (Exec.liftSt (PPState.state ×× PPState.iis) m1)
    (Exec.liftSt (PPState.state ×× PPState.iis) m2).
Proof.
  apply esim_liftSt.
  - intros [a1 m1' i1] [a2 m2' i2] (Hm & Ha & Hi & Hq). refine (conj _ (conj _ _)); assumption.
  - intros [a1 m1' i1] [a2 m2' i2] [t1 j1] [t2 j2] (Hm & Ha & Hi & Hq) (Ht & Hj & Hq').
    refine (conj _ (conj _ (conj _ _))); assumption.
Qed.

Lemma run_trans_end_sim te : esim pr_rel eq (run_trans_end te) (run_trans_end te).
Proof.
  unfold run_trans_end.
  bind tsr; [apply esim_pr_fst|]. destruct Hxy as [-> Hq].
  bind (iis_rel p); [apply esim_pr_snd|].
  destruct Hxy as (Hs & Ht & Hi & Hr & Hsr).
  destruct (IIS.trs x0) as [t1|], (IIS.trs y) as [t2|]; cbn in Ht; try contradiction;
    [|apply esim_throw].
  destruct Ht as (Hts & Hte & Hroot & Hrem).
  bind (@eq unit).
  { apply esim_mset. intros [a1 i1] [a2 i2] (Ha & Hi' & Hq'). cbn in *.
    refine (conj _ (conj _ _)); cbn; try assumption. apply (iis_rel_clear_trs _ Hp), Hi'. }
  bind (@eq unit); [apply esim_pr_add; exact Hts|].
  rewrite Hts.
  bind (@eq unit); [apply esim_pr_set_fst; [intro; symmetry; apply (map_vspec _ Hp)|reflexivity]|].
  destruct (decide _); [apply esim_ret; reflexivity|].
  cbn [ts_map TState.vrd TState.vwr TState.vdmbst TState.vdmb TState.vdsb TState.vcse TState.vacq].
  rewrite (map_ets3 _ Hp). fold_shift.
  rewrite (leb_shift _ Hp), Hte.
  destruct (_ <=? _); [|apply esim_discard].
  bind (@eq unit); [apply esim_pr_add; reflexivity|]. apply esim_pr_add; reflexivity.
Qed.

(** ** Register reads *)

Definition vvr {A} (a b : A * nat) := b = vv_map f a.

Lemma esim_mchoosel_map {St} (R : St → St → Prop) {A} (g : A → A) (l : list A) :
  esim R (λ x y, y = g x) (mchoosel l) (mchoosel (map g l)).
Proof.
  split; [|apply eerr_nil; reflexivity].
  intros s1 s2 s1' x Hs Hin. apply Exec.elem_of_mchoosel_inv in Hin as [-> Hx].
  exists s2, (g x). split; [apply Exec.elem_of_mchoosel, list_elem_of_fmap; eauto|auto].
Qed.

Lemma esim_othrow_map {St} (R : St → St → Prop) {A B} (V : A → B → Prop) (e1 e2 : string)
    (o : option A) (o' : option B) :
  option_rel V o o' → esim R V (othrow e1 o) (othrow e2 o').
Proof.
  intro Ho. apply esim_othrow.
  - intros x ->. destruct o'; [|contradiction]. eauto.
  - intros ->. destruct o'; [contradiction|reflexivity].
Qed.

Lemma option_rel_fmap {A B} (g : A → B) (o : option A) : option_rel (λ x y, y = g x) o (g <$> o).
Proof. destruct o; cbn; reflexivity || exact I. Qed.

Lemma esim_liftSt_fst {A B} (V : A → B → Prop) m1 m2 :
  esim tsr V m1 m2 → esim pr_rel V (Exec.liftSt fst m1) (Exec.liftSt fst m2).
Proof.
  apply esim_liftSt.
  - intros [a1 i1] [a2 i2] (Ha & Hi & Hq). split; assumption.
  - intros [a1 i1] [a2 i2] t1 t2 (Ha & Hi & Hq) [Ht Hq']. cbn in *.
    refine (conj _ (conj _ _)); assumption.
Qed.

Lemma run_reg_trans_read_sim reg racc t1 t2 : trs_rel p t1 t2 →
  esim tsr vvr (run_reg_trans_read reg racc t1) (run_reg_trans_read reg racc t2).
Proof.
  intros (_ & _ & Hroot & _). unfold run_reg_trans_read. rewrite Hroot.
  eapply esim_bind; [apply esim_guard_or_refl|intros ? ? _].
  eapply (esim_bind _ eq); [apply esim_othrow_map; destruct (IIS.TransRes.root t1); cbn; reflexivity || exact I
    |intros ? ? <-].
  destruct (decide _) as [Heq|]; [apply esim_ret; unfold vvr, vv_map; cbn; rewrite shift_zero by exact Hp;
    reflexivity|].
  bind tsr.
  { split; [|apply eerr_nil; reflexivity].
    intros s1 s2 s1' z Hs Hin. apply Exec.elem_of_mGet_inv in Hin as [-> ->].
    exists s2, s2. split; [apply Exec.elem_of_mGet|auto]. }
  destruct Hxy as [-> _].
  eapply esim_bind; [apply esim_guard_or_refl|intros ? ? _].
  apply esim_othrow_map. rewrite (map_read_reg _ Hp). apply option_rel_fmap.
Qed.

Lemma read_sreg_indirect_sim reg racc :
  esim pr_rel vvr (read_sreg_indirect reg racc) (read_sreg_indirect reg racc).
Proof.
  unfold read_sreg_indirect.
  bind (iis_rel p); [apply esim_pr_snd|].
  destruct Hxy as (_ & _ & _ & _ & Hsr). rewrite Hsr. unfold regs_map. rewrite dmap_lookup_map.
  destruct (dmap_lookup reg (IIS.sreg_reads x)) eqn:E; rewrite ?E; cbn.
  { apply esim_ret. reflexivity. }
  bind tsr; [apply esim_pr_fst|]. destruct Hxy as [-> Hq].
  bind (λ l l' : list (reg_type reg * view), l' = map (vv_map f) l).
  { apply esim_othrow_map. rewrite ts_map_read_sreg_indirect. apply option_rel_fmap. }
  subst y0. bind (λ a b : reg_type reg * view, b = vv_map f a); [apply esim_mchoosel_map|].
  subst y0.
  bind (@eq unit); [|apply esim_ret; reflexivity].
  apply esim_pr_set_snd. intros. apply (iis_rel_add_sreg_read _ Hp). assumption.
Qed.

Lemma run_reg_general_read_sim reg racc :
  esim pr_rel vvr (run_reg_general_read reg racc) (run_reg_general_read reg racc).
Proof.
  unfold run_reg_general_read.
  bind tsr; [apply esim_pr_fst|]. destruct Hxy as [-> Hq].
  destruct (decide _); [destruct (decide _)|].
  - apply esim_othrow_map. rewrite ts_map_read_sreg_direct. apply option_rel_fmap.
  - apply read_sreg_indirect_sim.
  - apply esim_othrow_map. rewrite (map_read_reg _ Hp). apply option_rel_fmap.
Qed.

Lemma run_reg_read_sim reg racc :
  esim pr_rel eq (run_reg_read reg racc) (run_reg_read reg racc).
Proof.
  unfold run_reg_read.
  bind (@vvr (reg_type reg)).
  { bind (iis_rel p); [apply esim_pr_snd|].
    destruct Hxy as (_ & Ht & _).
    destruct (IIS.trs x) as [t1|], (IIS.trs y) as [t2|]; cbn in Ht; try contradiction.
    - apply esim_liftSt_fst, run_reg_trans_read_sim, Ht.
    - apply run_reg_general_read_sim. }
  destruct x as [v1 w1], y as [v2 w2]. unfold vvr, vv_map in Hxy. cbn in Hxy.
  injection Hxy as -> ->. cbn.
  bind (@eq unit); [apply esim_pr_add; reflexivity|]. apply esim_ret. reflexivity.
Qed.

(** ** Write address announcements *)

Lemma announce_sim {A} (x : A) :
  esim pp_rel eq
    (vaddr ← mget (IIS.strict ∘ PPState.iis); ts ← mget PPState.state;
     guard_discard (TState.no_write_promises_until vaddr ts);;
     mset PPState.state (TState.update TState.vspec vaddr);; mret x)
    (vaddr ← mget (IIS.strict ∘ PPState.iis); ts ← mget PPState.state;
     guard_discard (TState.no_write_promises_until vaddr ts);;
     mset PPState.state (TState.update TState.vspec vaddr);; mret x).
Proof.
  bind vr; [apply esim_get_strict|]. unfold vr in Hxy. subst y.
  bind tsr; [apply esim_get_state|]. destruct Hxy as [-> _].
  gbind ltac:(apply (map_no_write_promises_until _ Hp)).
  bind (@eq unit); [apply esim_set_state; [intro; symmetry; apply (map_vspec _ Hp)|reflexivity]|].
  apply esim_ret. reflexivity.
Qed.

(** ** Register writes *)

Lemma natural_mapM_map {A B} (ga gb : A → stateT TLB.t (result string) B) (h : A → A) (l : list A) :
  (∀ x, x ∈ l → natural f (ga x) (gb (h x))) → natural f (mapM ga l) (mapM gb (map h l)).
Proof.
  intro Hg. induction l as [|x l IH]; cbn [mapM map]; [apply natural_ret|].
  apply natural_bind; [apply Hg; left|intro y].
  apply natural_bind; [apply IH; intros z Hz; apply Hg; right; exact Hz|intro].
  apply natural_ret.
Qed.

Lemma natural_othrow_some {A B} (e1 e2 : string) (a b : A) (ka kb : A → stateT TLB.t (result string) B) :
  natural f (ka a) (kb b) → natural f (othrow e1 (Some a) ≫= ka) (othrow e2 (Some b) ≫= kb).
Proof. intros H c. exact (H c). Qed.

Lemma add_wsreg_shifted (Hrc : tid ≠ rc) l reg val v ts :
  v ≤ length (l ++ r) →
  VMCacheState.roots_bounded (length (l ++ r)) (TState.read_sreg_indirect ts TTBR0_EL1) →
  VMCacheState.roots_bounded (length (l ++ r)) (TState.read_sreg_indirect ts TTBR1_EL1) →
  TState.add_wsreg tid imem (l ++ e :: r) reg val (f v) (ts_map f ts) =
  ts_map f <$> TState.add_wsreg tid imem (l ++ r) reg val v ts.
Proof.
  intros Hv H0 H1. unfold TState.add_wsreg.
  rewrite !ts_map_read_sreg_indirect.
  match goal with |- (TState.run_tlb ?ub _ ≫= _) = _ <$> (TState.run_tlb ?ua _ ≫= _) =>
    assert (Hn : natural f ua ub) end.
  2: { rewrite (run_tlb_map f _ _ ts Hn). destruct (TState.run_tlb _ ts) as [t|]; [|reflexivity].
       cbn. f_equal. }
  destruct reg as [r0|r0|r0|r0]; try apply natural_ret.
  destruct r0; try apply natural_ret; cbv beta iota zeta.
  - apply natural_bind; [apply fill_asid_root_shifted; assumption|intros _].
    apply natural_bind; [|intro; apply natural_ret].
    destruct (TState.read_sreg_indirect ts TTBR1_EL1) as [vs|]; cbn [default fmap option_fmap option_map];
      [|apply natural_ret].
    apply natural_mapM_map. intros [ttbr1 v1] Hin. cbn. unfold join, join_nat. rewrite <- shift_max.
    apply fill_asid_root_shifted; [exact Hrc|]. specialize (H1 _ Hin). cbn in H1.
    unfold join, join_nat. lia.
  - destruct (TState.read_sreg_indirect ts TTBR0_EL1) as [vs|]; cbn [default fmap option_fmap option_map];
      [|intro c; reflexivity].
    apply natural_othrow_some.
    apply natural_bind; [|intro; apply natural_ret].
    apply natural_mapM_map. intros [ttbr0 v0] Hin. cbn. unfold join, join_nat. rewrite <- shift_max.
    apply fill_asid_root_shifted; [exact Hrc|]. specialize (H0 _ Hin). cbn in H0.
    unfold join, join_nat. lia.
Qed.

(** Pointwise simulation from a fixed pair of states. *)
Definition esim_at {St A B} (R : St → St → Prop) (V : A → B → Prop)
    (m1 : Exec.t St string A) (m2 : Exec.t St string B) s1 s2 :=
  (∀ s1' x, Exec.elem_of_results (s1', x) (m1 s1) →
    ∃ s2' y, Exec.elem_of_results (s2', y) (m2 s2) ∧ R s1' s2' ∧ V x y) ∧
  (∀ s1' err, (s1', err) ∈ Exec.errors (m1 s1) →
    ∃ s2' err', (s2', err') ∈ Exec.errors (m2 s2) ∧ R s1' s2').

Lemma esim_at_of {St A B} (R : St → St → Prop) (V : A → B → Prop) m1 m2 s1 s2 :
  esim R V m1 m2 → R s1 s2 → esim_at R V m1 m2 s1 s2.
Proof. intros [Hr He] Hs. split; [intros; eapply Hr; eassumption|intros; eapply He; eassumption]. Qed.

Lemma esim_at_bind {St A1 A2 B1 B2} (R : St → St → Prop) (V1 : A1 → A2 → Prop) (V : B1 → B2 → Prop)
    m1 m2 k1 k2 s1 s2 :
  esim_at R V1 m1 m2 s1 s2 →
  (∀ s1' s2' x y, Exec.elem_of_results (s1', x) (m1 s1) → Exec.elem_of_results (s2', y) (m2 s2) →
    R s1' s2' → V1 x y → esim_at R V (k1 x) (k2 y) s1' s2') →
  esim_at R V (m1 ≫= k1) (m2 ≫= k2) s1 s2.
Proof.
  intros [Hm He] Hk. split.
  - intros s1' z Hin. apply Exec.elem_of_bind_elim in Hin as [mid [x [Hx Hz]]].
    destruct (Hm _ _ Hx) as [mid2 [y [Hy [Hmid Hv]]]].
    destruct (proj1 (Hk _ _ _ _ Hx Hy Hmid Hv) _ _ Hz) as [s2' [z' [Hz' [Hs' Hv']]]].
    exists s2', z'. split; [eapply Exec.elem_of_bind_intro; eassumption|auto].
  - intros s1' err Hin. apply errors_bind_elim in Hin as [Hin|(mid & x & Hx & Hin)].
    + destruct (He _ _ Hin) as [s2' [e' [He' Hs']]].
      exists s2', e'. split; [apply errors_bind_intro_l, He'|exact Hs'].
    + destruct (Hm _ _ Hx) as [mid2 [y [Hy [Hmid Hv]]]].
      destruct (proj2 (Hk _ _ _ _ Hx Hy Hmid Hv) _ _ Hin) as [s2' [e' [He' Hs']]].
      exists s2', e'. split; [eapply errors_bind_intro_r; eassumption|exact Hs'].
Qed.

Lemma esim_at_mget {St T1 T2 B1 B2} (R : St → St → Prop) (V : B1 → B2 → Prop)
    (g1 : St → T1) (g2 : St → T2) k1 k2 s1 s2 :
  R s1 s2 → esim_at R V (k1 (g1 s1)) (k2 (g2 s2)) s1 s2 →
  esim_at R V (mget g1 ≫= k1) (mget g2 ≫= k2) s1 s2.
Proof.
  intros Hs Hk. apply (esim_at_bind _ (λ x y, x = g1 s1 ∧ y = g2 s2)).
  - split; [|intros s1' err Hin; inversion Hin].
    intros s1' x Hin. apply Exec.elem_of_mget_inv in Hin as [-> ->].
    exists s2, (g2 s2). split; [apply Exec.elem_of_mget|auto].
  - intros s1' s2' x y Hin Hin2 _ [-> ->]. apply Exec.elem_of_mget_inv in Hin as [-> _].
    apply Exec.elem_of_mget_inv in Hin2 as [-> _]. exact Hk.
Qed.

Lemma esim_at_retain (prom : Promising.Model)
    (R : list (Promising.mEvent prom) * PPState.t (Promising.tState prom)
      (Promising.mEvent prom) (Promising.iis prom) → _ → Prop) old old' m1 m2 a b :
  old = old' → a.1 = b.1 → R a b → esim_at R eq m1 m2 a b →
  esim_at R eq (CPState.retain_new_candidates prom old m1)
    (CPState.retain_new_candidates prom old' m2) a b.
Proof.
  intros <- Hlists Hr [Hres Herr]. split; intros x ending Hin.
  - apply (retained_candidate_result prom) in Hin as [[Hgrow [-> ->]]|Hin].
    + exists b, CPState.StoppedEarly. split; [|auto]. apply (retained_candidate_result prom); left.
      rewrite <- Hlists. auto.
    + destruct (Hres _ _ Hin) as (y & r' & Hy & Hxy & Heq).
      exists y, r'. split; [apply (retained_candidate_continue prom), Hy|auto].
  - rewrite (retained_candidate_errors prom) in Hin.
    destruct (Herr _ _ Hin) as (y & err & Hy & Hxy).
    exists y, err. rewrite (retained_candidate_errors prom). auto.
Qed.

Ltac set_reg_fold :=
  match goal with |- context[TState.set_reg ?reg (?val, f ?x) (ts_map f ?t)] =>
    change (TState.set_reg reg (val, f x) (ts_map f t)) with
      (TState.set_reg reg (vv_map f (val, x)) (ts_map f t));
    rewrite (map_set_reg _ Hp) end.

Lemma run_reg_write_sim (Hrc : tid ≠ rc) reg racc val s1 s2 :
  pp_rel s1 s2 → VMViews.ok s1 →
  esim_at pp_rel eq (run_reg_write tid imem reg racc val) (run_reg_write tid imem reg racc val) s1 s2.
Proof.
  intros Hs Hok. unfold run_reg_write.
  apply (esim_at_bind _ eq); [apply esim_at_of; [apply esim_guard_or_refl|exact Hs]|].
  intros s1' s2' g g' Hin Hin2 Hs' <-. apply Exec.elem_of_guard_or_inv in Hin as ->.
  apply Exec.elem_of_guard_or_inv in Hin2 as ->.
  apply esim_at_mget; [exact Hs|]. apply esim_at_mget; [exact Hs|]. apply esim_at_mget; [exact Hs|].
  destruct s1 as [ts mem iis], s2 as [ts' mem' iis'], Hs as (Hm & Hts & Hi & Hq).
  cbn [PPState.state PPState.mem PPState.iis] in *. subst ts'.
  destruct Hok as [Hok Hiok]. cbn in Hok, Hiok.
  pose proof (VMViews.ok_strict _ _ Hiok) as Hstr.
  pose proof (VMViews.ok_vcse _ _ Hok). pose proof (VMViews.ok_vspec _ _ Hok).
  pose proof (VMViews.ok_vdsb _ _ Hok).
  destruct (VMViews.roots_ok _ _ Hok) as [Hr0 Hr1].
  destruct Hi as (Hs & Htr & Hinv & Hrmw & Hsr). rewrite Hs.
  apply esim_at_of; [|refine (conj Hm (conj eq_refl (conj _ Hq))); exact (conj Hs (conj Htr (conj Hinv (conj Hrmw Hsr))))].
  destruct Hm as (l & -> & ->).
  cbn [ts_map TState.vcse TState.vspec TState.vdsb]. fold_shift.
  destruct racc as [acc|].
  - bind vr.
    { destruct (decide (reg ∈ relaxed_regs)); [|destruct (decide (reg ∈ strict_regs))];
        [| |apply esim_throw].
      - bind (λ a b : reg_type reg * view, b = vv_map f a ∧ TState.read_sreg_direct ts reg = Some a).
        { apply esim_othrow_map. rewrite ts_map_read_sreg_direct.
          destruct (TState.read_sreg_direct ts reg); cbn; [split; reflexivity|exact I]. }
        destruct x as [x1 w], y as [y1 w'], Hxy as [Hxy Hrd]. unfold vv_map in Hxy. cbn in Hxy.
        injection Hxy as -> ->.
        pose proof (VMViews.read_sreg_direct_ok _ _ _ _ Hok Hrd) as Hw. cbn in Hw.
        fold_shift.
        bind tsr.
        {
          apply esim_lift_result.
          - intros nts Hn. rewrite (add_wsreg_shifted Hrc l), Hn; [| |exact Hr0|exact Hr1].
            + eexists. split; [reflexivity|]. split; [reflexivity|]. eapply add_wsreg_pos; eassumption.
            + unfold join, join_nat. lia.
          - intros err Hn. rewrite (add_wsreg_shifted Hrc l), Hn; [eauto| |exact Hr0|exact Hr1].
            unfold join, join_nat. lia. }
        bind (@eq unit); [apply esim_setv_state, Hxy|]. apply esim_ret. reflexivity.
      - bind tsr.
        { apply esim_othrow_map. set_reg_fold.
          destruct (TState.set_reg _ _ ts) eqn:E; cbn; [|exact I].
          split; [reflexivity|]. eapply set_reg_pos; eassumption. }
        bind (@eq unit); [apply esim_setv_state, Hxy|]. apply esim_ret. reflexivity. }
    rewrite Hxy.
    bind (@eq unit); [apply esim_set_state; [intro; symmetry; apply (map_vmsr _ Hp)|reflexivity]|].
    apply esim_add. reflexivity.
  - match goal with |- esim _ _ (if ?b then _ else _) _ => destruct b end.
    + gbind ltac:(apply (map_no_promises_until _ Hp)).
      bind (@eq unit); [apply esim_set_state; [intro; symmetry; apply (map_vspec _ Hp)|reflexivity]|].
      bind tsr; [apply esim_get_state|]. destruct Hxy as [-> Hq'].
      bind tsr.
      { apply esim_othrow_map. replace (val, 0) with (vv_map f (val, 0))
          by (unfold vv_map; cbn; rewrite shift_zero by exact Hp; reflexivity).
        rewrite (map_set_reg _ Hp).
        destruct (TState.set_reg _ _ x0) eqn:E; cbn; [|exact I].
        split; [reflexivity|]. eapply set_reg_pos; eassumption. }
      apply esim_setv_state, Hxy.
    + destruct (decide _); [|apply esim_throw].
      bind tsr.
      { apply esim_othrow_map. set_reg_fold.
        destruct (TState.set_reg _ _ ts) eqn:E; cbn; [|exact I].
        split; [reflexivity|]. eapply set_reg_pos; eassumption. }
      apply esim_setv_state, Hxy.
Qed.

End Handlers.

(** * Memory accesses, TLBIs, translations and whole instructions

    The remaining outcome handlers over the inserted history, and the
    pointwise simulation of [run_outcome] and [cinterp] from a pair of
    related instruction states whose shorter side satisfies [VMViews.ok]. *)

Section InsertMem.
Context (r : Memory.t) (tlbi : TLBI.t) (rc k : nat) (imem : memoryMap).
Local Notation p := (S (length r)).
Local Notation f := (shift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc k).

Lemma read_initial_insert addr size l :
  Memory.read_initial addr size imem (l ++ e :: r) = Memory.read_initial addr size imem (l ++ r).
Proof.
  unfold Memory.read_initial, PromMemory.read_initial.
  rewrite !length_app. cbn [length].
  rewrite (read_from_aux_insert Ev.get_msg addr size imem l r e (length r) (tlbi_not_msg _ _ _)).
  destruct (PromMemory.read_from_aux _ _ _ _ _ _) as [bytes|]; cbn; [|reflexivity].
  assert (Hz : ∀ t, (f t =? 0)%stdpp = (t =? 0)%stdpp).
  { intro t0. unfold shift. destruct (decide (t0 < p)); destruct t0; cbn; try reflexivity; lia. }
  induction bytes as [|[b t] bytes IH]; [reflexivity|]. cbn [mapM shift_bytes map fst snd] in *.
  unfold shift_bytes in IH. cbn. rewrite Hz.
  rewrite IH. reflexivity.
Qed.

Lemma read_all_aux_gt get_msg addr size (m : list Ev.t) tmin tmax : tmax < tmin →
  ∃ err, PromMemory.read_all_aux get_msg addr size imem m tmin tmax = Error err.
Proof.
  revert m. induction tmax as [|tmax IH]; intros m Hlt.
  - destruct m; cbn; case_bool_decide; try lia; eauto.
  - destruct m as [|x m]; cbn; case_bool_decide; try lia; [eauto|].
    destruct (IH m ltac:(lia)) as [err ->]. cbn. eauto.
Qed.

Lemma read_all_insert addr size l tmin :
  match Memory.read_all addr size imem (l ++ r) tmin,
        Memory.read_all addr size imem (l ++ e :: r) (f tmin) with
  | Ok c, Ok c' => c' = map (shift_bytes p) c
  | Error _, Error _ => True
  | _, _ => False
  end.
Proof.
  unfold Memory.read_all, PromMemory.read_all.
  destruct (decide (tmin ≤ length (l ++ r))) as [Hle|Hgt].
  - rewrite length_app in Hle |- *. rewrite length_app. cbn [length].
    rewrite (read_all_aux_insert Ev.get_msg addr size imem l r e tmin (length r)
      (tlbi_not_msg _ _ _) Hle).
    destruct (PromMemory.read_all_aux _ _ _ _ _ _ _); reflexivity || exact I.
  - destruct (read_all_aux_gt Ev.get_msg addr size (l ++ r) tmin (length (l ++ r)) ltac:(lia))
      as [e1 ->].
    destruct (read_all_aux_gt Ev.get_msg addr size (l ++ e :: r) (f tmin) (length (l ++ e :: r)))
      as [e2 ->]; [|exact I].
    rewrite insert_length, length_app. rewrite length_app in Hgt. rewrite shift_ge by lia. lia.
Qed.


Definition fb_map (x : bv 8 * nat * nat) : bv 8 * nat * nat := (x.1.1, f x.1.2, f x.2).

Lemma leb_shift_shift a b : (f a <=? f b) = (a <=? b).
Proof.
  pose proof (shift_le_iff p a b).
  destruct (Nat.leb_spec (f a) (f b)), (Nat.leb_spec a b); tauto || lia.
Qed.

Lemma read_fwd_map fwdb macc tread a :
  UMPromising.read_fwd (fwd_map f <$> fwdb) macc (f tread) a =
  fb_map <$> UMPromising.read_fwd fwdb macc tread a.
Proof.
  unfold UMPromising.read_fwd. rewrite lookup_fmap.
  destruct (fwdb !! a) as [fw|]; [|reflexivity]. cbn [fmap option_fmap option_map].
  destruct fw as [t v b x]. cbn [fwd_map FwdItem.time]. rewrite leb_shift_shift.
  destruct (tread <=? t); [|reflexivity]. cbn. unfold fb_map. cbn. f_equal. f_equal.
  unfold FwdItem.read_fwd_view. cbn. destruct x; [|reflexivity].
  destruct (is_rel_acq macc); [|reflexivity]. cbn. unfold join, join_nat. rewrite shift_max.
  reflexivity.
Qed.

Lemma fwd_bytes_map fwdb macc tread (addrs : list address) cand :
  map (λ '(addr, (byte, twrite)),
      UMPromising.read_fwd (fwd_map f <$> fwdb) macc (f tread) addr
      |> default (byte, f tread, twrite)) (zip addrs (shift_bytes p cand)) =
  map fb_map (map (λ '(addr, (byte, twrite)),
      UMPromising.read_fwd fwdb macc tread addr
      |> default (byte, tread, twrite)) (zip addrs cand)).
Proof.
  revert cand. induction addrs as [|a addrs IH]; intros [|[b t] cand]; try reflexivity.
  cbn [zip zip_with shift_bytes map fst snd]. cbn [map]. f_equal; [|apply IH].
  rewrite read_fwd_map. destruct (UMPromising.read_fwd fwdb macc tread a); reflexivity.
Qed.

Lemma foldr_max_map (l : list nat) : foldr max 0 (map f l) = f (foldr max 0 l).
Proof.
  induction l as [|x l IH]; cbn; [symmetry; apply shift_zero; lia|]. rewrite IH. apply eq_sym, shift_max.
Qed.

Lemma fb_map_parts (L : list (bv 8 * nat * nat)) :
  (map fb_map L).*1.*1 = L.*1.*1 ∧ (map fb_map L).*1.*2 = map f L.*1.*2 ∧
  (map fb_map L).*2 = map f L.*2.
Proof.
  induction L as [|[[b v] t] L IH]; [auto|]. destruct IH as (H1 & H2 & H3).
  cbn. rewrite H1, H2, H3. auto.
Qed.

Lemma zip_map_r {A} (addrs : list A) (ts : list nat) :
  zip addrs (map f ts) = map (λ av, (av.1, f av.2)) (zip addrs ts).
Proof.
  revert ts. induction addrs as [|a addrs IH]; intros [|t ts]; try reflexivity.
  cbn. f_equal. apply IH.
Qed.

Lemma coh_guard_map (coh : gmap address nat) (addrs : list address) (ts : list nat) :
  (∀ '(a, t) ∈ zip addrs ts, coh !!! a ≤ t) →
  ∀ '(a, t) ∈ zip addrs (map f ts), (f <$> coh) !!! a ≤ t.
Proof.
  intros H [a t] Hin. rewrite zip_map_r in Hin.
  apply list_elem_of_fmap in Hin as [[a0 t0] [Heq Hin]]. cbn in Heq. injection Heq as -> ->.
  specialize (H (a0, t0) Hin). cbn in H. rewrite (lookup_total_map p ltac:(lia)).
  apply shift_le_iff. exact H.
Qed.

Lemma nth_error_lookup' {A} (m : list A) i : nth_error m i = m !! i.
Proof. revert i. induction m as [|x m IH]; intros [|i]; cbn; auto. Qed.

(** The events strictly after [a] and at or before [c]. *)
Lemma slice_elem (m : Memory.t) a c x :
  x ∈ PromMemory.cut_after a (PromMemory.cut_before c m) ↔
  ∃ t, a < t ∧ t ≤ c ∧ mlookup m t = Some x.
Proof.
  unfold PromMemory.cut_after, PromMemory.cut_before. rewrite length_drop.
  split.
  - intro Hin. apply list_elem_of_lookup in Hin as [j Hj].
    apply lookup_take_Some in Hj as [Hj Hlt]. rewrite lookup_drop in Hj.
    pose proof (lookup_lt_Some _ _ _ Hj) as Hlen.
    exists (length m - (length m - c + j)). split; [lia|]. split; [lia|].
    rewrite lookup_spec. rewrite decide_True by lia. rewrite nth_error_lookup'.
    replace (length m - (length m - (length m - c + j))) with (length m - c + j) by lia. exact Hj.
  - intros (t & Ha & Hc & Hl). rewrite lookup_spec in Hl. case_decide as Ht; [|discriminate].
    rewrite nth_error_lookup' in Hl. apply list_elem_of_lookup.
    exists (length m - t - (length m - c)). apply lookup_take_Some. split; [|lia].
    rewrite lookup_drop. replace (length m - c + (length m - t - (length m - c))) with (length m - t)
      by lia. exact Hl.
Qed.

Lemma exclusive_insert tid addr size l a b :
  Memory.exclusive tid addr size (f a) (f b) (l ++ e :: r) ↔
  Memory.exclusive tid addr size a b (l ++ r).
Proof.
  unfold Memory.exclusive, PromMemory.exclusive. split; intros H x Hx.
  - apply slice_elem in Hx as (t & Ha & Hb & Hl). apply H, slice_elem.
    exists (f t). split; [apply shift_lt_iff; exact Ha|]. split; [|rewrite insert_lookup; exact Hl].
    assert (f t < f b) by (apply shift_lt_iff; lia). lia.
  - apply slice_elem in Hx as (t' & Ha & Hb & Hl).
    destruct (decide (t' = p)) as [->|Hne].
    { rewrite insert_lookup_new in Hl. injection Hl as <-. exact I. }
    remember (unshift p t') as u eqn:Hu.
    assert (t' = f u) by (subst u; symmetry; apply shift_unshift; lia). subst t'.
    rewrite insert_lookup in Hl. apply H, slice_elem.
    exists u. split; [apply shift_lt_iff in Ha; exact Ha|]. split; [|exact Hl].
    assert (u < b); [|lia].
    destruct (decide (u < b)) as [|Hge]; [assumption|].
    assert (f b ≤ f u) by (apply shift_le_iff; lia). lia.
Qed.

Lemma process_event_shifted tid l ev ts :
  TState.process_event tid imem (ev :: l ++ e :: r) ev (ts_map f ts) =
  ts_map f <$> TState.process_event tid imem (ev :: l ++ r) ev ts.
Proof.
  unfold TState.process_event.
  apply (run_tlb_map f (TLB.fill_promise tid imem (ev :: l ++ r) ev)
    (TLB.fill_promise tid imem (ev :: l ++ e :: r) ev) ts).
  exact (fill_promise_shifted tid imem l r tlbi rc k ev).
Qed.

(** ** Removal of the event: reads and exclusivity at collapsed timestamps

    For the removal direction a timestamp [t'] of the longer history is
    read at [unshift p t'] of the shorter one; [p] collapses onto [p - 1]. *)
Lemma read_all_remove addr size l t' :
  match Memory.read_all addr size imem (l ++ r) (unshift p t'),
        Memory.read_all addr size imem (l ++ e :: r) t' with
  | Ok c, Ok c' => c' = map (shift_bytes p) c
  | Error _, Error _ => True
  | _, _ => False
  end.
Proof.
  destruct (decide (t' = p)) as [->|Hne].
  - rewrite unshift_ge by lia. cbn [pred].
    unfold Memory.read_all, PromMemory.read_all. rewrite !length_app. cbn [length].
    rewrite (read_all_aux_insert_at Ev.get_msg addr size imem l r e (length r) (tlbi_not_msg _ _ _)).
    destruct (PromMemory.read_all_aux _ _ _ _ _ _ _); reflexivity || exact I.
  - pose proof (read_all_insert addr size l (unshift p t')) as H.
    rewrite (shift_unshift p t' Hne ltac:(lia)) in H. exact H.
Qed.

Lemma exclusive_remove tid addr size l a' b' : b' ≠ p →
  Memory.exclusive tid addr size a' b' (l ++ e :: r) →
  Memory.exclusive tid addr size (unshift p a') (unshift p b') (l ++ r).
Proof.
  unfold Memory.exclusive, PromMemory.exclusive. intros Hb H x Hx.
  apply slice_elem in Hx as (t & Ha & Htb & Hl). apply H, slice_elem.
  exists (f t). split; [apply lt_shift_iff; lia|]. split; [|rewrite insert_lookup; exact Hl].
  assert (Hlt : unshift p (f t) < unshift p b') by (rewrite unshift_shift; lia).
  apply unshift_lt_iff_ne in Hlt; [lia|exact Hb|lia].
Qed.

End InsertMem.

Section InsertRun.
Context (r : Memory.t) (tlbi : TLBI.t) (rc k : nat) (n_threads tid : nat) (imem : memoryMap).
Local Notation p := (S (length r)).
Local Notation f := (shift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc k).
Local Notation pp_rel := (pp_rel r tlbi rc k).
Local Notation mem_rel := (mem_rel r tlbi rc k).
Local Notation tsr := (tsr r).
Local Notation vr := (vr r).
Local Notation Hp := (Hp r).
Local Notation esim_get_state := (esim_get_state r tlbi rc k).
Local Notation esim_get_strict := (esim_get_strict r tlbi rc k).
Local Notation esim_get_mem := (esim_get_mem r tlbi rc k).
Local Notation esim_get_iis := (esim_get_iis r tlbi rc k).
Local Notation esim_set_state := (esim_set_state r tlbi rc k).
Local Notation esim_set_iis := (esim_set_iis r tlbi rc k).
Local Notation esim_add := (esim_add r tlbi rc k).
Set Default Proof Using "Type".

Ltac bind V := eapply (esim_bind _ V); [|
  let x := fresh "x" in let y := fresh "y" in let H := fresh "Hxy" in intros x y H;
  lazymatch type of x with unit => clear H; destruct x, y | _ => idtac end].

Ltac bind_subst V := eapply (esim_bind _ V);
  [|let y := fresh "y" in let H := fresh in intros ? y H; cbv beta in H; subst y].

Ltac gbind tac := eapply esim_bind;
  [apply esim_guard_discard; let HG := fresh "HG" in intro HG; tac; exact HG|intros ? ? _].

Ltac fold_shift :=
  unfold join, join_nat in *;
  repeat first [rewrite (shift_view_if _ Hp)|rewrite <- shift_max].

Lemma read_mem_explicit_sim addr size macc :
  esim pp_rel eq (read_mem_explicit imem addr size macc) (read_mem_explicit imem addr size macc).
Proof.
  unfold read_mem_explicit.
  bind constr:(tsr); [apply esim_get_state|]. destruct Hxy as [-> Hq].
  bind constr:(vr); [apply esim_get_strict|]. unfold vr in Hxy. subst y.
  gbind ltac:(apply (map_no_promises_until _ Hp)).
  cbn [ts_map TState.vrd TState.vwr TState.vdmb TState.vdsb TState.vcse TState.vacq TState.vrel
    TState.vspec TState.fwdb TState.coh].
  rewrite (map_min_cohs _ Hp). fold_shift.
  bind constr:(mem_rel); [apply esim_get_mem|]. destruct Hxy as (l & -> & ->).
  bind_subst (λ c c', c' = map (shift_bytes p) c).
  { match goal with |- context [Memory.read_all _ _ _ (l ++ r) ?t] =>
      pose proof (read_all_insert r tlbi rc k imem addr size l t) as Hra end.
    apply esim_lift_result.
    - intros c Hc. rewrite Hc in Hra.
      destruct (Memory.read_all _ _ _ (l ++ e :: r) _); [|contradiction]. eauto.
    - intros err Hc. rewrite Hc in Hra.
      destruct (Memory.read_all _ _ _ (l ++ e :: r) _); [contradiction|]. eauto. }
  bind_subst (λ c c', c' = shift_bytes p c); [apply esim_mchoosel_map|].
  rewrite (max_list_with_shift p _ Hp).
  rewrite fwd_bytes_map.
  match goal with |- context [map (fb_map _) ?L] => destruct (fb_map_parts r L) as (H1 & H2 & H3) end.
  rewrite H1, H2, H3, foldr_max_map. fold_shift.
  bind (@eq unit).
  { destruct (is_atomic_rmw macc); [|apply esim_ret; reflexivity].
    apply esim_msetv. intros [a1 m1 i1] [a2 m2 i2] (Hm & Ha & Hi & Hq'). cbn in *.
    refine (conj Hm (conj Ha (conj _ Hq'))).
    destruct Hi as (Hs & Ht & Hi' & Hr & Hsr). destruct i1, i2; cbn in *.
    refine (conj _ (conj _ (conj _ (conj _ _)))); cbn; first [assumption|reflexivity]. }
  gbind ltac:(apply coh_guard_map).
  bind_subst (λ o o' : option nat, o' = f <$> o).
  { apply esim_mget. intros s1 s2 (_ & _ & Hi & _). apply Hi. }
  bind (@eq unit).
  { apply esim_guard_discard'. match goal with |- context [if ?o is Some _ then _ else _] =>
      destruct o end; cbn; [apply shift_lt_iff|auto]. }
  rewrite (zip_map_r r).
  bind (@eq unit); [apply esim_set_state; [intro; symmetry; apply (map_update_cohs _ Hp)
    |apply update_cohs_tlb]|].
  bind (@eq unit); [apply esim_set_state; [intro; symmetry; apply (map_vrd _ Hp)|reflexivity]|].
  bind (@eq unit); [apply esim_set_state; [intro; symmetry; apply (map_vacq _ Hp)|reflexivity]|].
  bind (@eq unit); [apply esim_set_state; [intro; symmetry; apply (map_vspec _ Hp)|reflexivity]|].
  bind (@eq unit).
  { destruct (is_exclusive macc); [|apply esim_ret; reflexivity].
    apply esim_set_state; [intro; symmetry; apply (map_set_xclb _ Hp)|reflexivity]. }
  bind (@eq unit); [apply esim_add; reflexivity|]. apply esim_ret. reflexivity.
Qed.

Lemma promise_eq ev (m : Memory.t) : Memory.promise ev m = Exec.make [(ev :: m, S (length m))] [].
Proof. reflexivity. Qed.

Lemma promise_lift_errors ev (s : PPState.t TState.t Ev.t IIS.t) :
  Exec.errors (Exec.liftSt PPState.mem (Memory.promise ev) s) = [].
Proof. reflexivity. Qed.

Lemma promise_lift_inv ev (s s' : PPState.t TState.t Ev.t IIS.t) t :
  Exec.elem_of_results (s', t) (Exec.liftSt PPState.mem (Memory.promise ev) s) →
  s' = setv PPState.mem (ev :: PPState.mem s) s ∧ t = S (length (PPState.mem s)).
Proof.
  intro H. apply Exec.elem_of_liftSt_inv in H as [m [-> H]]. rewrite promise_eq in H.
  apply list_elem_of_singleton in H. injection H as -> ->. auto.
Qed.

Lemma promise_lift_intro ev (s : PPState.t TState.t Ev.t IIS.t) :
  Exec.elem_of_results (setv PPState.mem (ev :: PPState.mem s) s, S (length (PPState.mem s)))
    (Exec.liftSt PPState.mem (Memory.promise ev) s).
Proof. apply Exec.elem_of_liftSt. rewrite promise_eq. left. Qed.

(** A new event promised on both histories, followed by a read of the
    history. *)
Lemma esim_promise_block {B1 B2} (V : B1 → B2 → Prop) ev
    (K1 : nat → Memory.t → Exec.t (PPState.t TState.t Ev.t IIS.t) string B1)
    (K2 : nat → Memory.t → Exec.t (PPState.t TState.t Ev.t IIS.t) string B2) :
  (∀ l', esim pp_rel V (K1 (S (length (l' ++ r))) (ev :: l' ++ r))
    (K2 (f (S (length (l' ++ r)))) (ev :: l' ++ e :: r))) →
  esim pp_rel V
    (time ← Exec.liftSt PPState.mem (Memory.promise ev); mem ← mget PPState.mem; K1 time mem)
    (time ← Exec.liftSt PPState.mem (Memory.promise ev); mem ← mget PPState.mem; K2 time mem).
Proof.
  intros HK.
  assert (Hrel : ∀ s1 s2, pp_rel s1 s2 → ∃ l', PPState.mem s1 = l' ++ r ∧
    PPState.mem s2 = l' ++ e :: r ∧
    pp_rel (setv PPState.mem (ev :: PPState.mem s1) s1) (setv PPState.mem (ev :: PPState.mem s2) s2)).
  { intros [a1 m1 i1] [a2 m2 i2] ((l' & Hm1 & Hm2) & Ha & Hi & Hq). cbn in *. subst m1 m2.
    exists l'. split; [reflexivity|]. split; [reflexivity|].
    refine (conj _ (conj Ha (conj Hi Hq))). exists (ev :: l'). split; reflexivity. }
  split.
  - intros s1 s2 s1' x Hs Hin.
    apply Exec.elem_of_bind_elim in Hin as [mid [t [Ht Hk]]].
    apply promise_lift_inv in Ht as [-> ->].
    apply Exec.elem_of_bind_elim in Hk as [mid' [m [Hm Hk]]].
    apply Exec.elem_of_mget_inv in Hm as [-> ->].
    destruct (Hrel s1 s2 Hs) as (l' & Hm1 & Hm2 & Hs').
    cbn [PPState.mem setv] in Hk |- *. rewrite Hm1 in Hk, Hs'. rewrite Hm2 in Hs'.
    destruct (proj1 (HK l') _ _ _ _ Hs' Hk) as [s2' [y [Hy [HR HV]]]].
    exists s2', y. split; [|auto].
    eapply Exec.elem_of_bind_intro; [apply promise_lift_intro|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    cbn [PPState.mem setv]. rewrite Hm2.
    replace (S (length (l' ++ e :: r))) with (f (S (length (l' ++ r)))); [exact Hy|].
    rewrite insert_length, shift_ge by (rewrite length_app; lia). reflexivity.
  - intros s1 s2 s1' err Hs Hin.
    apply errors_bind_elim in Hin as [Hin|(mid & t & Ht & Hin)];
      [rewrite promise_lift_errors in Hin; inversion Hin|].
    apply promise_lift_inv in Ht as [-> ->].
    apply errors_bind_elim in Hin as [Hin|(mid' & m & Hm & Hin)];
      [unfold mget in Hin; inversion Hin|].
    apply Exec.elem_of_mget_inv in Hm as [-> ->].
    destruct (Hrel s1 s2 Hs) as (l' & Hm1 & Hm2 & Hs').
    cbn [PPState.mem setv] in Hin |- *. rewrite Hm1 in Hin, Hs'. rewrite Hm2 in Hs'.
    destruct (proj2 (HK l') _ _ _ _ Hs' Hin) as [s2' [err' [He HR]]].
    exists s2', err'. split; [|exact HR].
    eapply errors_bind_intro_r; [apply promise_lift_intro|].
    eapply errors_bind_intro_r; [apply Exec.elem_of_mget|].
    cbn [PPState.mem setv]. rewrite Hm2.
    replace (S (length (l' ++ e :: r))) with (f (S (length (l' ++ r)))); [exact He|].
    rewrite insert_length, shift_ge by (rewrite length_app; lia). reflexivity.
Qed.

Lemma write_mem_sim addr size macc data :
  esim pp_rel (λ o o', o' = f <$> o)
    (write_mem tid imem addr size macc data) (write_mem tid imem addr size macc data).
Proof.
  unfold write_mem.
  bind constr:(tsr); [apply esim_get_state|]. destruct Hxy as [-> Hq].
  bind constr:(mem_rel); [apply esim_get_mem|]. destruct Hxy as (l & -> & ->).
  cbn [ts_map TState.prom_wr]. rewrite (fulfill_insert_tlbi l r).
  bind (λ a b : nat * bool, b.1 = f a.1 ∧ b.2 = a.2).
  { destruct (Memory.fulfill _ _ (l ++ r)) as [time|]; cbn [fmap option_fmap option_map].
    - apply esim_ret. auto.
    - apply esim_promise_block. intro l'.
      bind constr:(tsr).
      { apply esim_lift_result.
        - intros nts Hn. rewrite process_event_shifted, Hn. eexists. split; [reflexivity|].
          split; [reflexivity|]. eapply process_event_pos; [|exact Hq|exact Hn]. cbn. lia.
        - intros err Hn. rewrite process_event_shifted, Hn. eauto. }
      bind (@eq unit); [apply esim_setv_state, Hxy|]. apply esim_ret. auto. }
  destruct x0 as [time np], y as [time' np'], Hxy as [Ht Hn]. cbn in Ht, Hn. subst time' np'.
  bind (@eq bool).
  { destruct (is_atomic_rmw macc); [|apply esim_ret; reflexivity].
    bind_subst (λ o o' : option (nat * bool), o' = (λ tb : nat * bool, (f tb.1, tb.2)) <$> o).
    { apply esim_mget. intros s1 s2 (_ & _ & Hi & _). apply Hi. }
    eapply (esim_bind _ (λ a b : nat * bool, b = (f a.1, a.2)));
      [apply esim_othrow_map, option_rel_fmap|intros [tread ra] ? ->]. cbn [fst snd].
    bind (@eq unit); [apply esim_guard_discard'; apply exclusive_insert|].
    bind (@eq unit).
    { apply esim_msetv. intros [a1 m1 i1] [a2 m2 i2] (Hm & Ha & Hi & Hq'). cbn in *.
      refine (conj Hm (conj Ha (conj _ Hq'))).
      destruct Hi as (Hs & Ht & Hi' & Hr & Hsr). destruct i1, i2; cbn in *.
      refine (conj _ (conj _ (conj _ (conj _ _)))); cbn; first [assumption|reflexivity]. }
    apply esim_ret. reflexivity. }
  subst y.
  bind constr:(vr); [apply esim_get_strict|]. unfold vr in Hxy. subst y.
  cbn [ts_map TState.vrd TState.vwr TState.vdmb TState.vdmbst TState.vdsb TState.vcse
    TState.vacq TState.vrel TState.vspec TState.coh TState.xclb].
  fold_shift.
  gbind ltac:(destruct HG as [HG1 HG2]; split;
    [apply shift_lt_iff, HG1
    |intros a Ha; rewrite (lookup_total_map p ltac:(lia)); apply shift_lt_iff, HG2, Ha]).
  bind_subst (λ o o' : option nat, o' = f <$> o).
  { apply esim_mget. intros s1 s2 (_ & _ & Hi & _). apply Hi. }
  bind (@eq unit).
  { apply esim_guard_discard'. match goal with |- context [if ?o is Some _ then _ else _] =>
      destruct o end; cbn; [apply shift_lt_iff|auto]. }
  bind (@eq unit).
  { apply esim_mset. intros [a1 m1 i1] [a2 m2 i2] (Hm & Ha & Hi & Hq'). cbn in *. subst a2.
    refine (conj Hm (conj _ (conj Hi _))).
    - symmetry. apply (map_filter_prom_wr _ Hp).
    - destruct a1; exact Hq'. }
  replace (map (λ x : bv addr_size, (x, f time)) (addr_range addr size)) with
    (map (λ av, (av.1, f av.2)) (map (λ x : bv addr_size, (x, time)) (addr_range addr size)))
    by (rewrite map_map; reflexivity).
  bind (@eq unit); [apply esim_set_state; [intro; symmetry; apply (map_update_cohs _ Hp)
    |apply update_cohs_tlb]|].
  bind (@eq unit); [apply esim_set_state; [intro; symmetry; apply (map_vwr _ Hp)|reflexivity]|].
  bind (@eq unit); [apply esim_set_state; [intro; symmetry; apply (map_vrel _ Hp)|reflexivity]|].
  bind (@eq unit).
  { destruct (_ && _ && _); [|apply esim_ret; reflexivity].
    apply esim_set_state; [intro; symmetry; apply (map_vacq _ Hp)|reflexivity]. }
  bind_subst (λ o o' : option nat, o' = f <$> o).
  { destruct (is_exclusive macc); [|apply esim_ret; reflexivity].
    destruct (TState.xclb x) as [xcl|]; cbn [fmap option_fmap option_map]; [|apply esim_discard].
    bind (@eq unit); [apply esim_set_state; [intro; symmetry; apply (map_clear_xclb _ Hp)
      |reflexivity]|].
    destruct xcl as [xt xa xs xv]. cbn [xcl_map XclItem.addr XclItem.size XclItem.time XclItem.view].
    destruct (decide _); [|apply esim_discard].
    bind (@eq unit); [apply esim_guard_discard'; apply exclusive_insert|].
    apply esim_ret. reflexivity. }
  bind (@eq unit); [apply esim_set_state; [intro; symmetry; apply (map_set_fwdbs _ Hp)
    |apply set_fwdbs_tlb]|].
  apply esim_ret. destruct np; reflexivity.
Qed.

Lemma materialize_sim vpre vpre' tl recipient : vpre' = f vpre →
  esim pp_rel (λ a b : nat * bool, b.1 = f a.1 ∧ b.2 = a.2)
    (materialize_tlbi_for_recipient tid imem vpre tl recipient)
    (materialize_tlbi_for_recipient tid imem vpre' tl recipient).
Proof.
  intros ->. unfold materialize_tlbi_for_recipient.
  bind constr:(tsr); [apply esim_get_state|]. destruct Hxy as [-> Hq].
  bind constr:(mem_rel); [apply esim_get_mem|]. destruct Hxy as (l & -> & ->).
  cbn [ts_map TState.prom_tlbi TState.dsb_epoch]. rewrite (fulfill_insert_tlbi l r).
  bind (λ a b : nat * bool, b.1 = f a.1 ∧ b.2 = a.2).
  { destruct (Memory.fulfill _ _ (l ++ r)) as [time|]; cbn [fmap option_fmap option_map].
    - apply esim_ret. auto.
    - apply esim_promise_block. intro l'.
      bind constr:(tsr).
      { apply esim_lift_result.
        - intros nts Hn. rewrite process_event_shifted, Hn. eexists. split; [reflexivity|].
          split; [reflexivity|]. eapply process_event_pos; [|exact Hq|exact Hn]. cbn. lia.
        - intros err Hn. rewrite process_event_shifted, Hn. eauto. }
      bind (@eq unit); [apply esim_setv_state, Hxy|]. apply esim_ret. auto. }
  destruct x0 as [time np], y as [time' np'], Hxy as [Ht Hn]. cbn in Ht, Hn. subst time' np'.
  gbind ltac:(apply shift_lt_iff).
  bind (@eq unit).
  { apply esim_mset. intros [a1 m1 i1] [a2 m2 i2] (Hm & Ha & Hi & Hq'). cbn in *. subst a2.
    refine (conj Hm (conj _ (conj Hi _))).
    - symmetry. apply (map_filter_prom_tlbi _ Hp).
    - destruct a1; exact Hq'. }
  apply esim_ret. auto.
Qed.

Lemma esim_foldlM_rel {St A1 A2 B} (R : St → St → Prop) (VA : A1 → A2 → Prop)
    (f1 : A1 → B → Exec.t St string A1) (f2 : A2 → B → Exec.t St string A2) a1 a2 l :
  (∀ a1 a2 x, VA a1 a2 → esim R VA (f1 a1 x) (f2 a2 x)) → VA a1 a2 →
  esim R VA (foldlM f1 a1 l) (foldlM f2 a2 l).
Proof.
  intros Hf. revert a1 a2. induction l as [|x l IH]; intros a1 a2 Ha; cbn [foldlM];
    [apply esim_ret, Ha|].
  apply (esim_bind _ VA); [apply Hf, Ha|]. intros ? ? H. apply IH, H.
Qed.

Lemma run_tlbi_sim viio viio' tlbiinfo : viio' = f viio →
  esim pp_rel (λ o o', o' = f <$> o)
    (run_tlbi n_threads tid imem viio tlbiinfo) (run_tlbi n_threads tid imem viio' tlbiinfo).
Proof.
  intros ->. unfold run_tlbi.
  eapply esim_bind; [apply esim_guard_or_refl|intros ? ? _].
  bind constr:(tsr); [apply esim_get_state|]. destruct Hxy as [-> Hq].
  bind (iis_rel p); [apply esim_get_iis|]. destruct Hxy as (Hs & _). rewrite Hs.
  cbn [ts_map TState.vcse TState.vdsb TState.vspec]. fold_shift.
  bind_subst (@eq TLBI.t).
  { destruct (TLBIRecord_op _); first [apply esim_ret; reflexivity|apply esim_throw]. }
  eapply (esim_bind _ (λ a b : nat * nat * bool, b.1.1 = f a.1.1 ∧ b.1.2 = f a.1.2 ∧ b.2 = a.2)).
  { apply esim_foldlM_rel; [|cbn; rewrite shift_zero by lia; auto].
    intros [[vs vo] cr] [[vs' vo'] cr'] recipient (H1 & H2 & H3). cbn in H1, H2, H3. subst.
    eapply (esim_bind _ (λ a b : nat * bool, b.1 = f a.1 ∧ b.2 = a.2));
      [apply materialize_sim; reflexivity|].
    intros [t1 n1] [t2 n2] [Ht Hn]. cbn in Ht, Hn. subst.
    apply esim_ret. cbn. destruct (decide (recipient = tid)); cbn; rewrite ?shift_max; auto. }
  intros [[vs vo] cr] [[vs' vo'] cr'] (H1 & H2 & H3). cbn in H1, H2, H3. subst.
  cbv beta iota.
  bind (@eq unit).
  { apply esim_set_state; [|reflexivity]. intro t. unfold compose.
    rewrite <- (map_vtlbi_self _ Hp), <- (map_vtlbi_other _ Hp). reflexivity. }
  fold_shift.
  bind (@eq unit); [apply esim_add; reflexivity|]. apply esim_ret. destruct cr; reflexivity.
Qed.

Lemma min_promise_le vmax ts : TState.min_promise vmax ts ≤ vmax + 1.
Proof.
  unfold TState.min_promise. generalize (TState.prom_wr ts ++ TState.prom_tlbi ts).
  intro L. induction L; cbn; lia.
Qed.

Lemma pred_shift_le a M : a ≤ pred M → f a ≤ pred (f M).
Proof.
  intro H. destruct (decide (a < M)) as [Hlt|Hge].
  - apply (proj2 (shift_lt_iff p a M)) in Hlt. lia.
  - assert (a = 0 ∧ M = 0) as [-> ->] by lia. rewrite shift_zero by lia. lia.
Qed.

Lemma pred_shift_lt M V : pred M < V ↔ pred (f M) < f V.
Proof.
  destruct M as [|M].
  - rewrite shift_zero by lia. cbn. pose proof (shift_lt_iff p 0 V). rewrite shift_zero in H by lia.
    lia.
  - pose proof (shift_le_iff p (S M) V). assert (0 < f (S M)) by shift_cases. cbn. lia.
Qed.

Lemma map_tcohs_before asid offs o ts :
  TState.tcohs_before_inv_time asid offs o ts →
  TState.tcohs_before_inv_time asid offs (f <$> o) (ts_map f ts).
Proof.
  destruct o as [t|]; cbn; [|auto]. intros H po Hin. unfold TState.get_tcoh in *.
  cbn [ts_map TState.tcoh]. rewrite (lookup_total_map p ltac:(lia)). apply shift_lt_iff, H, Hin.
Qed.

Lemma run_trans_start_sim start :
  esim pp_rel eq (run_trans_start tid imem start) (run_trans_start tid imem start).
Proof.
  unfold run_trans_start.
  bind constr:(tsr); [apply esim_get_state|]. destruct Hxy as [-> Hq].
  bind (iis_rel p); [apply esim_get_iis|]. destruct Hxy as (Hs & _). rewrite Hs.
  bind constr:(mem_rel); [apply esim_get_mem|]. destruct Hxy as (l & -> & ->).
  rewrite (map_ets2 _ Hp).
  cbn [ts_map TState.vcse TState.vdsb TState.vwr TState.vrd]. fold_shift.
  assert (HM : TState.min_promise (length (l ++ e :: r)) (ts_map f x) =
    f (TState.min_promise (length (l ++ r)) x)).
  { apply (map_min_promise _ Hp). rewrite insert_length, shift_ge by (rewrite length_app; lia).
    lia. }
  rewrite HM. pose proof (min_promise_le (length (l ++ r)) x) as HMle.
  eapply esim_bind; [apply esim_guard_or_refl|intros ? ? _].
  gbind ltac:(apply pred_shift_le).
  assert (Hb : pred (f (TState.min_promise (length (l ++ r)) x)) ≤ S (length (l ++ r))).
  { pose proof (shift_le_iff p (TState.min_promise (length (l ++ r)) x) (S (length (l ++ r)))).
    rewrite (shift_ge p (S (length (l ++ r)))) in H by (rewrite length_app; lia). lia. }
  pose proof (unshift_pred_shift p (TState.min_promise (length (l ++ r)) x) Hp) as Hmax.
  eapply (esim_bind _ (λ a b : IIS.TransRes.t * option nat,
    trs_rel p a.1 b.1 ∧ b.2 = f <$> a.2)).
  { destruct (is_upper_va _) as [upper|].
    - bind_subst (@eq reg); [apply (esim_lift_result _ eq); intros; eauto|].
      eapply (esim_bind _ (@vvr r (bv 64))).
      { apply (esim_liftSt_pr r tlbi rc k). exact (read_sreg_indirect_sim r TTBR0_EL1 None). }
      intros [t0 v0] [t1 v1] Hv. unfold vvr, vv_map in Hv. cbn in Hv. injection Hv as <- ->.
      eapply esim_bind; [apply esim_guard_or_refl|intros ? ? _].
      match goal with |- context [TState.tlb_lookup tid imem (l ++ r) x ?ifc ?up ?vpn ?asid ?t0
          ?tmo ?tmu ?tmax] =>
        destruct (tlb_lookup_merge_map tid imem l r tlbi rc k ifc up vpn x (ts_map f x) asid t0
          tmo tmu tmax (pred (f (TState.min_promise (length (l ++ r)) x))) eq_refl Hq
          (ts_map_read_sreg_indirect _ _ _) Hmax Hb) as [HF HE] end.
      eapply esim_bind.
      { apply esim_guard_or; cbn [Exec.results Exec.errors]; intros H Hr He.
        - rewrite <- HE in He. apply (proj1 (pred_shift_lt _ _)), H; [|exact He].
          apply Forall2_length in HF. destruct (TLB.Result.merge _); [reflexivity|].
          rewrite Hr in HF. discriminate.
        - rewrite HE in He. apply (proj2 (pred_shift_lt _ _)), H; [|exact He].
          apply Forall2_length in HF. destruct (TLB.Result.merge (Exec.results (TState.tlb_lookup
            _ _ (l ++ e :: r) _ _ _ _ _ _ _ _ _))); [reflexivity|].
          rewrite Hr in HF. discriminate. }
      intros ? ? _.
      eapply (esim_bind _ (res_rel p)).
      { apply esim_lift_res.
        - intros res Hres. cbn in Hres. apply list_elem_of_lookup in Hres as [i Hi].
          destruct (Forall2_lookup_l _ _ _ _ _ HF Hi) as [y' [Hy Hr]].
          exists y'. split; [apply list_elem_of_lookup; eauto|exact Hr].
        - intros err Herr. exists err. cbn in Herr |- *. rewrite <- HE. exact Herr. }
      intros res res' (Hr1 & Hr2 & Hr3 & Hr4 & Hr5). rewrite Hr1.
      eapply (esim_bind _ eq); [apply esim_othrow; [intros ? ->; eauto|auto]|intros ? ? <-].
      apply esim_ret. cbn. split; [|exact Hr5]. refine (conj Hr3 (conj Hr4 (conj eq_refl _))).
      cbn. exact Hr2.
    - apply esim_ret. cbn. split; [|reflexivity]. refine (conj eq_refl (conj Hmax _)).
      split; reflexivity. }
  intros [tres inv] [tres' inv'] [Htr Hinv]. cbn in Htr, Hinv. subst inv'. cbv beta iota.
  gbind ltac:(apply map_tcohs_before).
  destruct Htr as (Hts & Hte & Hroot & Hrem). rewrite Hts.
  bind (@eq unit); [apply esim_set_state; [intro; symmetry; apply (map_update_tcohs _ Hp)
    |apply update_tcohs_tlb]|].
  bind (@eq unit).
  { apply esim_set_iis. intros. apply (iis_rel_set_trs _ Hp); [assumption|].
    exact (conj Hts (conj Hte (conj Hroot Hrem))). }
  apply esim_set_iis. intros. apply (iis_rel_set_inv_time _ Hp). assumption.
Qed.

Lemma read_imem_insert addr l :
  read_imem imem addr (l ++ e :: r) = read_imem imem addr (l ++ r).
Proof. unfold read_imem. rewrite (read_initial_insert r tlbi rc k). reflexivity. Qed.

Lemma esim_get_mem_len :
  esim pp_rel (λ m m' : Memory.t, f (length m) ≤ length m') (mget PPState.mem) (mget PPState.mem).
Proof. apply esim_mget. intros s1 s2 (H & _). apply (mem_rel_length_le r tlbi rc k), H. Qed.

Lemma esim_at_fmap {St A1 A2 B1 B2} (R : St → St → Prop) (V1 : A1 → A2 → Prop)
    (V : B1 → B2 → Prop) m1 m2 (g1 : A1 → B1) (g2 : A2 → B2) s1 s2 :
  esim_at R V1 m1 m2 s1 s2 → (∀ x y, V1 x y → V (g1 x) (g2 y)) →
  esim_at R V (g1 <$> m1) (g2 <$> m2) s1 s2.
Proof.
  intros [Hm He] Hg. split.
  - intros s1' z Hin. apply Exec.elem_of_fmap_inv in Hin as [x [-> Hx]].
    destruct (Hm _ _ Hx) as [s2' [y [Hy [Hs' Hv]]]].
    exists s2', (g2 y). split; [apply Exec.elem_of_fmap_intro, Hy|auto].
  - intros s1' err Hin. exact (He s1' err Hin).
Qed.

Definition out_rel {A} (x y : A * option nat) := x.1 = y.1 ∧ y.2 = f <$> x.2.

Lemma run_outcome_sim (Hrc : tid ≠ rc) out s1 s2 : pp_rel s1 s2 → VMViews.ok s1 →
  esim_at pp_rel out_rel (run_outcome n_threads tid imem out)
    (run_outcome n_threads tid imem out) s1 s2.
Proof.
  intros Hs Hok.
  Local Ltac mem_handler := match goal with H : shift _ (length _) ≤ length _ |- _ =>
    first [apply run_barrier_sim; [assumption|exact H]|apply run_cse_sim; [assumption|exact H]
          |apply run_take_exception_sim; [assumption|exact H]] end.
  destruct out.
  all: lazymatch goal with
    | |- context [run_outcome _ _ _ (MemRead ?mr)] => destruct mr as [? ? ? ? [|?]]
    | |- context [run_outcome _ _ _ (MemWrite ?mr _ _)] => destruct mr as [? ? ? ? [|?]]
    | _ => idtac end.
  all: simp run_outcome.
  all: try (apply esim_at_of; [|exact Hs]; apply esim_throw).
  all: try solve [apply esim_at_of; [|exact Hs]; first
    [ bind (λ m m' : Memory.t, f (length m) ≤ length m'); [apply esim_get_mem_len|];
      bind (@eq unit); [mem_handler|]; apply esim_ret; split; reflexivity
    | bind constr:(vr); [apply esim_get_strict|];
      bind_subst (λ o o' : option nat, o' = f <$> o); [apply run_tlbi_sim, Hxy|];
      apply esim_ret; split; reflexivity
    | bind (@eq unit); [apply run_trans_start_sim|]; apply esim_ret; split; reflexivity
    | bind (@eq unit); [apply (esim_liftSt_pr r tlbi rc k), run_trans_end_sim|];
      apply esim_ret; split; reflexivity ]].
  - (* RegRead *)
    apply esim_at_of; [|exact Hs].
    bind (@eq (reg_type reg0)); [apply (esim_liftSt_pr r tlbi rc k), run_reg_read_sim|].
    subst. apply esim_ret. split; reflexivity.
  - (* RegWrite *)
    apply (esim_at_bind _ eq); [apply run_reg_write_sim; assumption|].
    intros s1' s2' u u' _ _ Hs' _. apply esim_at_of; [|exact Hs'].
    apply esim_ret. split; reflexivity.
  - (* MemRead *)
    apply esim_at_of; [|exact Hs].
    eapply esim_bind; [apply esim_guard_or_refl|intros ? ? _].
    destruct (is_ifetch _); [|destruct (is_explicit _); [|destruct (is_ttw _)]].
    + eapply esim_bind; [apply esim_guard_or_refl|intros ? ? <-].
      bind constr:(mem_rel); [apply esim_get_mem|]. destruct Hxy as (l & -> & ->).
      rewrite read_imem_insert.
      eapply (esim_bind _ eq).
      { apply esim_lift_res; [intros ? H; eexists; split; [exact H|reflexivity]
          |intros ? H; eexists; exact H]. }
      intros ? ? <-. apply esim_ret. split; reflexivity.
    + eapply (esim_bind _ eq); [apply read_mem_explicit_sim|intros ? ? <-].
      apply esim_ret. split; reflexivity.
    + eapply esim_bind; [apply esim_guard_or_refl|intros ? ? <-].
      eapply (esim_bind _ eq); [apply read_pte_sim|intros ? ? <-].
      apply esim_ret. split; reflexivity.
    + apply esim_throw.
  - (* MemWriteAddrAnnounce *)
    apply esim_at_of; [|exact Hs].
    bind constr:(vr); [apply esim_get_strict|]. unfold vr in Hxy. subst y.
    bind constr:(tsr); [apply esim_get_state|]. destruct Hxy as [-> _].
    gbind ltac:(apply (map_no_write_promises_until _ Hp)).
    bind (@eq unit); [apply esim_set_state; [intro; symmetry; apply (map_vspec _ Hp)|reflexivity]|].
    apply esim_ret. split; reflexivity.
  - (* MemWrite *)
    apply esim_at_of; [|exact Hs].
    eapply esim_bind; [apply esim_guard_or_refl|intros ? ? _].
    eapply esim_bind; [apply esim_guard_or_refl|intros ? ? _].
    bind_subst (λ o o' : option nat, o' = f <$> o); [apply write_mem_sim|].
    apply esim_ret. split; reflexivity.
Qed.

Lemma cinterp_sim (Hrc : tid ≠ rc) {A} (mon : iMon A) s1 s2 : pp_rel s1 s2 → VMViews.ok s1 →
  esim_at pp_rel eq (cinterp (run_outcome' n_threads tid imem) mon)
    (cinterp (run_outcome' n_threads tid imem) mon) s1 s2.
Proof.
  revert s1 s2. induction mon as [a|call kont IH]; intros s1 s2 Hs Hok.
  - cbn. apply esim_at_of; [apply esim_ret; reflexivity|exact Hs].
  - destruct call as [out|[m]]; cbn.
    + apply (esim_at_bind _ eq).
      * apply (esim_at_fmap _ out_rel); [apply run_outcome_sim; assumption|].
        intros x y [H _]. exact H.
      * intros s1' s2' x y Hin _ Hs' <-. apply IH; [exact Hs'|].
        apply Exec.elem_of_fmap_inv in Hin as [x' [_ Hx']].
        eapply VMViews.run_outcome_ok; eassumption.
    + apply (esim_at_bind _ eq); [apply esim_at_of; [apply esim_mchoose|exact Hs]|].
      intros s1' s2' x y Hin _ Hs' <-. apply Exec.elem_of_mchoose_inv in Hin as ->.
      apply IH; assumption.
Qed.

(** An instruction of a thread that is not the recipient of the inserted
    TLBI, run from related instruction states: every result and every error
    state of the shorter run has a related counterpart of the longer run. *)
Theorem instruction_insert_sim (Hrc : tid ≠ rc) {A} (mon : iMon A) s1 s2 :
  pp_rel s1 s2 → VMViews.ok s1 →
  (∀ s1' ret, Exec.elem_of_results (s1', ret) (cinterp (run_outcome' n_threads tid imem) mon s1) →
    ∃ s2', Exec.elem_of_results (s2', ret) (cinterp (run_outcome' n_threads tid imem) mon s2) ∧
      pp_rel s1' s2') ∧
  (∀ s1' err, (s1', err) ∈ Exec.errors (cinterp (run_outcome' n_threads tid imem) mon s1) →
    ∃ s2' err', (s2', err') ∈ Exec.errors (cinterp (run_outcome' n_threads tid imem) mon s2) ∧
      pp_rel s1' s2').
Proof.
  intros Hs Hok. destruct (cinterp_sim Hrc mon s1 s2 Hs Hok) as [Hr He]. split; [|exact He].
  intros s1' ret Hin. destruct (Hr _ _ Hin) as [s2' [y [Hy [HR <-]]]]. eauto.
Qed.
End InsertRun.


(** * Broadcast of fresh events, thread by thread *)

Section Broadcast.
Context (bbm : bool) {n : nat}.
Local Notation prom := (VMPromising bbm).

(** The deliveries of [PState.broadcast_fresh] to one thread. *)
Fixpoint bcast_thread (owner : fin n) (imem : memoryMap) (base extra : list Ev.t) (i : fin n)
    (ts : TState.t) : result string TState.t :=
  match extra with
  | [] => mret ts
  | ev :: older =>
      ts' ← bcast_thread owner imem base older i ts;
      if decide (i = owner) then mret ts'
      else TState.emit_promise i imem (ev :: older ++ base) ev ts'
  end.

Lemma vimapM_intro' {A B E m} (g : fin m → A → result E B) (xs : vec A m) (ys : vec B m) :
  (∀ i, g i (xs !!! i) = Ok (ys !!! i)) → vimapM g xs = Ok ys.
Proof.
  revert g ys. induction xs as [|x m xs IH]; intros g ys.
  - inv_vec ys. reflexivity.
  - inv_vec ys. intros y ys Hg. cbn [vimapM].
    pose proof (Hg 0%fin) as H0. cbn in H0. rewrite H0. cbn.
    rewrite (IH (g ∘ FS) ys (λ i, Hg (FS i))). reflexivity.
Qed.

Lemma broadcast_fresh_lookup owner imem base extra (states states' : vec TState.t n) :
  PState.broadcast_fresh prom owner imem base extra states = Ok states' →
  ∀ i, bcast_thread owner imem base extra i (states !!! i) = Ok (states' !!! i).
Proof.
  revert states'. induction extra as [|ev extra IH]; intros states' Hrun i.
  - injection Hrun as <-. reflexivity.
  - cbn [PState.broadcast_fresh] in Hrun.
    destruct (PState.broadcast_fresh prom owner imem base extra states) as [mid|err] eqn:Hmid;
      [|discriminate].
    cbn [mbind result_bind] in Hrun. cbn [bcast_thread]. rewrite (IH mid eq_refl i). cbn.
    exact (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hrun i).
Qed.

Lemma broadcast_fresh_intro owner imem base extra (states states' : vec TState.t n) :
  (∀ i, bcast_thread owner imem base extra i (states !!! i) = Ok (states' !!! i)) →
  PState.broadcast_fresh prom owner imem base extra states = Ok states'.
Proof.
  revert states'. induction extra as [|ev extra IH]; intros states' Hall.
  - cbn. f_equal. apply vec_eq. intro i. specialize (Hall i). cbn in Hall.
    injection Hall as ->. reflexivity.
  - cbn [PState.broadcast_fresh].
    assert (Hmid : ∀ i, ∃ t, bcast_thread owner imem base extra i (states !!! i) = Ok t).
    { intro i. specialize (Hall i). cbn [bcast_thread] in Hall.
      destruct (bcast_thread owner imem base extra i (states !!! i)); [eauto|discriminate]. }
    set (mid := fun_to_vec (λ i, match bcast_thread owner imem base extra i (states !!! i) with
      | Ok t => t | Error _ => states !!! i end)).
    assert (Hm : ∀ i, bcast_thread owner imem base extra i (states !!! i) = Ok (mid !!! i)).
    { intro i. unfold mid. rewrite lookup_fun_to_vec. destruct (Hmid i) as [t ->]. reflexivity. }
    rewrite (IH mid Hm). cbn. apply vimapM_intro'. intro i.
    specialize (Hall i). cbn [bcast_thread] in Hall. rewrite Hm in Hall. exact Hall.
Qed.
End Broadcast.

Section BroadcastInsert.
Context (r : Memory.t) (tlbi : TLBI.t) (rc k : nat).
Local Notation p := (S (length r)).
Local Notation f := (shift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc k).

Lemma bcast_thread_insert {n} (owner : fin n) imem l extra i ts :
  bcast_thread owner imem (l ++ e :: r) extra i (ts_map f ts) =
  ts_map f <$> bcast_thread owner imem (l ++ r) extra i ts.
Proof.
  induction extra as [|ev older IH]; [reflexivity|]. cbn [bcast_thread]. rewrite IH.
  destruct (bcast_thread owner imem (l ++ r) older i ts) as [t|]; cbn; [|reflexivity].
  destruct (decide (i = owner)); [reflexivity|].
  rewrite !app_assoc. apply emit_promise_shifted.
Qed.

Lemma bcast_thread_pos {n} (owner : fin n) imem base extra i ts ts' : ts_pos ts →
  bcast_thread owner imem base extra i ts = Ok ts' → ts_pos ts'.
Proof.
  revert ts'. induction extra as [|ev older IH]; intros ts' Hq H; cbn [bcast_thread] in H.
  - injection H as <-. exact Hq.
  - destruct (bcast_thread owner imem base older i ts) as [t|] eqn:Ht; [|discriminate].
    cbn in H. destruct (decide _); [injection H as <-; exact (IH t Hq eq_refl)|].
    eapply emit_promise_pos; [|exact (IH t Hq eq_refl)|exact H]. cbn. lia.
Qed.
End BroadcastInsert.

Section RunTidInsert.
Context (r : Memory.t) (tlbi : TLBI.t) (rc k : nat) (bbm : bool) {n : nat} (isem : iMon ()).
Local Notation p := (S (length r)).
Local Notation f := (shift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc k).
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).

(** One instruction of a thread [tid] that is not the recipient of the
    inserted TLBI. The shorter run decomposes into the instruction and the
    per-thread deliveries of its fresh events [extra]; the longer state runs
    the same instruction to the shifted thread state, and reaches every
    state whose threads receive [extra] on the longer history. *)
Theorem run_tid_insert (tid : fin n) (s s' s1 : state) l :
  (tid : nat) ≠ rc →
  PState.initmem s' = PState.initmem s →
  PState.events s = l ++ r → PState.events s' = l ++ e :: r →
  PState.tstate tid s' = ts_map f (PState.tstate tid s) →
  ts_pos (PState.tstate tid s) →
  VMViews.ts_ok (length (PState.events s)) (PState.tstate tid s) →
  Exec.elem_of_results (s1, ()) (PState.run_tid isem prom tid s) →
  ∃ extra ts1,
    PState.initmem s1 = PState.initmem s ∧
    PState.events s1 = extra ++ l ++ r ∧ ts_pos ts1 ∧
    (∀ i, bcast_thread tid (PState.initmem s) (l ++ r) extra i
      (vinsert tid ts1 (PState.tstates s) !!! i) = Ok (PState.tstates s1 !!! i)) ∧
    (∀ states', (∀ i, bcast_thread tid (PState.initmem s) (l ++ e :: r) extra i
        (vinsert tid (ts_map f ts1) (PState.tstates s') !!! i) = Ok (states' !!! i)) →
      Exec.elem_of_results (PState.Make states' (PState.initmem s) (extra ++ l ++ e :: r), ())
        (PState.run_tid isem prom tid s')).
Proof.
  intros Hrc Himem Hl Hl' Hts Hq Hok Hrun.
  destruct (run_tid_broadcast_decompose prom isem tid s s1 Hrun)
    as [ts [mem [iis [states [Hinst [Hb ->]]]]]].
  assert (Hinit : VMViews.ok (PPState.Make (PState.tstate tid s) (PState.events s) IIS.init)).
  { split; [exact Hok|]. eapply VMViews.iis_ok_mono; [|exact VMViews.iis_init]. lia. }
  destruct (VMViews.instruction_ok n tid (PState.initmem s) isem _ _ () Hinit Hinst)
    as [_ [extra Hextra]].
  cbn in Hextra. subst mem.
  assert (Hrel : pp_rel r tlbi rc k (PPState.Make (PState.tstate tid s) (PState.events s) IIS.init)
    (PPState.Make (PState.tstate tid s') (PState.events s') IIS.init)).
  { refine (conj _ (conj Hts (conj (iis_rel_init p ltac:(lia)) Hq))). exists l. auto. }
  destruct (proj1 (instruction_insert_sim r tlbi rc k n tid (PState.initmem s) Hrc isem _ _ Hrel
    Hinit) _ () Hinst) as [[ts' mem' iis'] [Hinst' (Hm & Hts' & _ & Hq')]].
  cbn in Hm, Hts', Hq'. subst ts'. destruct Hm as (l1 & Hm1 & ->).
  rewrite Hl in Hm1. assert (l1 = extra ++ l) as ->.
  { rewrite app_assoc in Hm1. symmetry. eapply app_inv_tail. exact Hm1. }
  rewrite length_app, Nat.add_sub, take_app_length in Hb.
  exists extra, ts. split; [reflexivity|]. split; [cbn; rewrite Hl; reflexivity|].
  split; [exact Hq'|]. split.
  { rewrite <- Hl. exact (broadcast_fresh_lookup bbm tid _ _ _ _ _ Hb). }
  intros states' Hall. rewrite app_assoc.
  replace (PState.initmem s) with (PState.initmem s') by exact Himem.
  apply run_tid_broadcast_intro with (ts := ts_map f ts) (iis := iis').
  - rewrite Himem. exact Hinst'.
  - rewrite Hl', <- app_assoc, length_app, Nat.add_sub, take_app_length.
    apply broadcast_fresh_intro. rewrite Himem. exact Hall.
Qed.
End RunTidInsert.

(** * Positive TLBI times along the traces of the normalization *)

Section TracePos.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n).
Local Notation state := (PState.t TState.t Ev.t n).

Lemma inst_pos (s s' : state) : state_pos s →
  InstructionTransition (VMPromising bbm) nondet term s s' →
  state_pos s'.
Proof. intros Hq [t [_ Hrun]]. eapply run_tid_pos; eassumption. Qed.

Lemma rawstep_pos ev (s s' : state) : state_pos s →
  VMNormalization.RawStep bbm nondet term ev s s' → state_pos s'.
Proof. intros Hq [_ Hp]. eapply promise_pos; eassumption. Qed.

Lemma mixed_pos (s s' : state) : state_pos s →
  VMNormalization.Mixed bbm nondet term s s' → state_pos s'.
Proof.
  intros Hq [Hi|[ev Hr]]; [eapply inst_pos; eassumption|eapply rawstep_pos; eassumption].
Qed.

Lemma mixed_rtc_pos (s s' : state) : state_pos s →
  rtc (VMNormalization.Mixed bbm nondet term) s s' → state_pos s'.
Proof. intros Hq H. induction H; [exact Hq|]. apply IHrtc. eapply mixed_pos; eassumption. Qed.

Lemma raw_trace_pos (s s' : state) evs : state_pos s →
  VMNormalization.RawTrace bbm nondet term s evs s' → state_pos s'.
Proof.
  intros Hq H. induction H as [|evs mid s' ev _ IH Hstep]; [exact Hq|].
  eapply rawstep_pos; [exact IH|exact Hstep].
Qed.
End TracePos.

End VMSwapInsert.
