(******************************************************************************)
(* Thread updates after removal of a TLBI                                     *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMSwapSim PromiseFirstSailVMSwapLookup
  PromiseFirstSailVMSwapRemoveRun.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveMap.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemoveRun.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Section Map.
Context (p : nat) (Hp : 0 < p).
Set Default Proof Using "All".
Local Notation f := (unshift p).

Ltac map_fields :=
  match goal with ts : TState.t |- _ => destruct ts end;
  unfold TState.update, TState.set_xclb, TState.clear_xclb, TState.promise_write,
    TState.promise_tlbi, setv, set, ts_map;
  cbn -[unshift regs_map dmap_map fmap map lev_map tlb_map fwd_map xcl_map];
  rewrite ?unshift_max; reflexivity.

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

Lemma lookup_total_map {K} `{Countable K} (m : gmap K nat) a : (f <$> m) !!! a = f (m !!! a).
Proof using Hp.
  rewrite !lookup_total_alt, lookup_fmap. destruct (m !! a); cbn; [reflexivity|].
  symmetry. apply unshift_zero.
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
  rewrite lookup_total_map, <- unshift_max.
  destruct t. unfold set, ts_map. cbn -[unshift regs_map dmap_map fmap map lev_map tlb_map fwd_map xcl_map].
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
  cbn -[unshift regs_map dmap_map fmap map lev_map tlb_map fwd_map xcl_map partial_alter].
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
  cbn -[unshift regs_map dmap_map fmap map lev_map tlb_map xcl_map].
  rewrite fmap_insert. reflexivity.
Qed.

Lemma map_set_reg reg vv ts :
  TState.set_reg reg (vv_map f vv) (ts_map f ts) = ts_map f <$> TState.set_reg reg vv ts.
Proof.
  unfold TState.set_reg. cbn [ts_map TState.regs]. unfold regs_map.
  rewrite dmap_lookup_map.
  destruct (dmap_lookup reg (TState.regs ts)) eqn:E; rewrite ?E; cbn.
  - rewrite !decide_True by auto. cbn. f_equal.
    destruct ts. unfold set, ts_map. cbn -[unshift dmap_map fmap map lev_map tlb_map fwd_map xcl_map].
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

Lemma foldr_min_map base base' (l : list nat) : base' = f base →
  foldr (λ q v, v `min` q) base' (map f l) = f (foldr (λ q v, v `min` q) base l).
Proof.
  intros ->. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite IH. shift_cases.
Qed.

(** The sentinel for [min_promise] must map with the history bound. *)
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
  unfold TState.min_cohs. destruct addrs as [|a addrs]; [symmetry; apply unshift_zero|].
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

Lemma unshift_view_if b x : view_if b (f x) = f (view_if b x).
Proof using Hp. unfold view_if, UMPromising.view_if. destruct b; [reflexivity|]. symmetry. apply unshift_zero. Qed.


(** Strict promise guards are preserved when no promise names the removed
    event. This is the condition needed for a foreign TLBI. *)
Definition promises_avoid (ts : TState.t) : Prop :=
  Forall (λ t, t ≠ p) (TState.prom_wr ts ++ TState.prom_tlbi ts).

Lemma map_no_promises_until v ts : promises_avoid ts →
  TState.no_promises_until (f v) (ts_map f ts) ↔ TState.no_promises_until v ts.
Proof using Hp.
  intro Hne. unfold promises_avoid in Hne. rewrite list.Forall_forall in Hne.
  unfold TState.no_promises_until. cbn [ts_map TState.prom_wr TState.prom_tlbi].
  rewrite <- map_app. split; intros H q Hq.
  - apply (proj1 (unshift_lt_iff_ne p v q (Hne q Hq) Hp)), H, list_elem_of_fmap. eauto.
  - apply list_elem_of_fmap in Hq as [q0 [-> Hq0]].
    apply (proj2 (unshift_lt_iff_ne p v q0 (Hne q0 Hq0) Hp)), H, Hq0.
Qed.

Lemma map_no_write_promises_until v ts : Forall (λ t, t ≠ p) (TState.prom_wr ts) →
  TState.no_write_promises_until (f v) (ts_map f ts) ↔ TState.no_write_promises_until v ts.
Proof using Hp.
  intro Hne. rewrite list.Forall_forall in Hne. unfold TState.no_write_promises_until.
  cbn [ts_map TState.prom_wr]. split; intros H q Hq.
  - apply (proj1 (unshift_lt_iff_ne p v q (Hne q Hq) Hp)), H, list_elem_of_fmap. eauto.
  - apply list_elem_of_fmap in Hq as [q0 [-> Hq0]].
    apply (proj2 (unshift_lt_iff_ne p v q0 (Hne q0 Hq0) Hp)), H, Hq0.
Qed.

Lemma filter_map_ne (l : list nat) t : t ≠ p → Forall (λ x, x ≠ p) l →
  filter (λ x, x ≠ f t) (map f l) = map f (filter (λ x, x ≠ t) l).
Proof.
  clear Hp. intros Ht. induction 1 as [|x l Hx Hl IH]; [reflexivity|].
  cbn [map]. rewrite !filter_cons. pose proof (unshift_eq_ne p x t Hx Ht).
  repeat case_decide; first [exact IH|cbn; rewrite IH; reflexivity|exfalso; naive_solver].
Qed.

Lemma map_filter_prom_wr t ts : t ≠ p → Forall (λ x, x ≠ p) (TState.prom_wr ts) →
  ts_map f (set TState.prom_wr (filter (λ x, x ≠ t)) ts) =
  set TState.prom_wr (filter (λ x, x ≠ f t)) (ts_map f ts).
Proof.
  intros Ht Hl. destruct ts. unfold set, ts_map.
  cbn -[unshift regs_map dmap_map fmap map lev_map tlb_map fwd_map xcl_map filter].
  rewrite filter_map_ne by assumption. reflexivity.
Qed.

Lemma map_filter_prom_tlbi t ts : t ≠ p → Forall (λ x, x ≠ p) (TState.prom_tlbi ts) →
  ts_map f (set TState.prom_tlbi (filter (λ x, x ≠ t)) ts) =
  set TState.prom_tlbi (filter (λ x, x ≠ f t)) (ts_map f ts).
Proof.
  intros Ht Hl. destruct ts. unfold set, ts_map.
  cbn -[unshift regs_map dmap_map fmap map lev_map tlb_map fwd_map xcl_map filter].
  rewrite filter_map_ne by assumption. reflexivity.
Qed.

Lemma min_promise_avoids vmax ts : S vmax ≠ p → promises_avoid ts → TState.min_promise vmax ts ≠ p.
Proof.
  clear Hp. unfold promises_avoid, TState.min_promise. rewrite Nat.add_1_r.
  generalize (TState.prom_wr ts ++ TState.prom_tlbi ts). intros l Hb Hl.
  induction Hl as [|t l Ht Hl IH]; [exact Hb|]. cbn.
  destruct (Nat.le_ge_cases (foldr (λ q v, v `min` q) (S vmax) l) t).
  - rewrite Nat.min_l by assumption. exact IH.
  - rewrite Nat.min_r by assumption. exact Ht.
Qed.

Lemma cse_candidates_map vpre vmax vmax' ts v :
  promises_avoid ts → f vmax ≤ vmax' → v ∈ TState.cse_candidates vpre vmax ts →
  f v ∈ TState.cse_candidates (f vpre) vmax' (ts_map f ts).
Proof using Hp.
  intros Hne Hmax Hin. unfold TState.cse_candidates in *. apply elem_of_seq in Hin. apply elem_of_seq.
  set (L := TState.prom_wr ts ++ TState.prom_tlbi ts).
  assert (Hm : TState.min_promise vmax' (ts_map f ts) = foldr (λ q w, w `min` q) (vmax' + 1) (map f L)).
  { unfold TState.min_promise, L. cbn [ts_map TState.prom_wr TState.prom_tlbi]. rewrite map_app. reflexivity. }
  assert (Hm0 : TState.min_promise vmax ts = foldr (λ q w, w `min` q) (vmax + 1) L) by reflexivity.
  rewrite Hm. rewrite Hm0 in Hin.
  assert (Hlt : ∀ (l : list nat) b b', Forall (λ q, q ≠ p) l →
    v < foldr (λ q w, w `min` q) b l → f v < b' →
    f v < foldr (λ q w, w `min` q) b' (map f l)).
  { intros l b b' Hl. induction Hl as [|q l Hq Hl IH]; intros H1 H2; cbn in *; [exact H2|].
    apply Nat.min_glb_lt; [apply IH; lia|apply (proj2 (unshift_lt_iff_ne p v q Hq Hp)); lia]. }
  assert (Hb : ∀ l b, foldr (λ q w, w `min` q) b l ≤ b) by (intros l0 b; induction l0; cbn; lia).
  pose proof (Hb L (vmax + 1)).
  pose proof (unshift_mono p vpre v ltac:(lia)). pose proof (unshift_mono p v vmax ltac:(lia)).
  assert (f v < foldr (λ q w, w `min` q) (vmax' + 1) (map f L))
    by (apply (Hlt L (vmax + 1)); [exact Hne|lia|lia]).
  lia.
Qed.
End Map.
End VMSwapRemoveMap.
