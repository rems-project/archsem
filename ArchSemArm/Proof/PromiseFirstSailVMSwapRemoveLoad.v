(******************************************************************************)
(* Explicit-load simulation after removing a foreign TLBI                      *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheSim PromiseFirstSailVMSwapSim
  PromiseFirstSailVMSwapLookup PromiseFirstSailVMSwapInsert PromiseFirstSailVMSwapRemoveRun
  PromiseFirstSailVMSwapRemoveMap PromiseFirstSailVMSwapRemoveLocal PromiseFirstSailVMSwapRemoveRead
  PromiseFirstSailVMSwapRemoveTimes PromiseFirstSailVMSwapRemoveStamps PromiseFirstSailVMSwapRemoveViews.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveLoad.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemoveRun VMSwapRemoveLocal VMCacheSimOutcome.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Definition bytes_map (f : nat → nat) (bytes : list (bv 8 * nat)) := map (λ bt, (bt.1, f bt.2)) bytes.
Definition fb_map (f : nat → nat) (x : bv 8 * nat * nat) := (x.1.1, f x.1.2, f x.2).
Lemma bytes_unshift_shift p bytes : bytes_map (unshift p) (shift_bytes p bytes) = bytes.
Proof.
  unfold bytes_map, shift_bytes. induction bytes as [|[b t] bytes IH]; cbn;
    rewrite ?unshift_shift, ?IH; reflexivity.
Qed.
Lemma fb_map_parts f (L : list (bv 8 * nat * nat)) :
  (map (fb_map f) L).*1.*1 = L.*1.*1 ∧ (map (fb_map f) L).*1.*2 = map f L.*1.*2 ∧
  (map (fb_map f) L).*2 = map f L.*2.
Proof.
  induction L as [|[[b v] t] L IH]; [auto|]. destruct IH as (H1 & H2 & H3).
  cbn. rewrite H1, H2, H3. auto.
Qed.
Lemma zip_map_r {A} (f : nat → nat) (addrs : list A) (ts : list nat) :
  zip addrs (map f ts) = map (λ av, (av.1, f av.2)) (zip addrs ts).
Proof. revert ts. induction addrs as [|a addrs IH]; intros [|t ts]; try reflexivity. cbn. f_equal. apply IH. Qed.

Section Map.
Context (p : nat) (Hp : 0 < p).
Local Notation g := (unshift p).
Lemma read_fwd_map fwdb macc tread addr : tread ≠ p →
  UMPromising.read_fwd (fwd_map g <$> fwdb) macc (g tread) addr =
  fb_map g <$> UMPromising.read_fwd fwdb macc tread addr.
Proof using Hp.
  intro Htime. unfold UMPromising.read_fwd. rewrite lookup_fmap.
  destruct (fwdb !! addr) as [[time v byte xcl]|]; [|reflexivity]. cbn [fmap option_fmap option_map fwd_map FwdItem.time].
  assert (Hle : (g tread <=? g time) = (tread <=? time)).
  { pose proof (unshift_le_iff_ne p tread time Htime Hp).
    destruct (Nat.leb_spec (g tread) (g time)), (Nat.leb_spec tread time); tauto || lia. }
  rewrite Hle. destruct (tread <=? time); [|reflexivity]. cbn. unfold fb_map. cbn. f_equal. f_equal.
  unfold FwdItem.read_fwd_view. cbn. destruct xcl; [|reflexivity].
  destruct (is_rel_acq macc); [|reflexivity]. cbn. unfold join, join_nat. rewrite unshift_max. reflexivity.
Qed.
Lemma fwd_bytes_map fwdb macc tread (addrs : list address) cand : tread ≠ p →
  map (λ '(addr, (byte, twrite)), UMPromising.read_fwd (fwd_map g <$> fwdb) macc (g tread) addr
    |> default (byte, g tread, twrite)) (zip addrs (bytes_map g cand)) =
  map (fb_map g) (map (λ '(addr, (byte, twrite)), UMPromising.read_fwd fwdb macc tread addr
    |> default (byte, tread, twrite)) (zip addrs cand)).
Proof using Hp.
  intro Htime. revert cand. induction addrs as [|a addrs IH]; intros [|[b t] cand]; try reflexivity.
  cbn [zip zip_with bytes_map map fst snd]. cbn [map]. f_equal; [|apply IH].
  rewrite read_fwd_map by exact Htime. destruct (UMPromising.read_fwd fwdb macc tread a); reflexivity.
Qed.
Lemma foldr_max_map (l : list nat) : foldr max 0 (map g l) = g (foldr max 0 l).
Proof.
  induction l as [|x l IH]; cbn; [symmetry; apply unshift_zero|]. rewrite IH. symmetry. apply unshift_max.
Qed.
Lemma max_bytes bytes : max_list_with snd (bytes_map g bytes) = g (max_list_with snd bytes).
Proof.
  induction bytes as [|[b t] bytes IH]; cbn [bytes_map max_list_with map fst snd];
    [symmetry; apply unshift_zero|]. rewrite IH. symmetry. apply unshift_max.
Qed.
Lemma coh_guard_map (coh : gmap address nat) (addrs : list address) (ts : list nat) :
  (∀ '(a, t) ∈ zip addrs ts, coh !!! a ≤ t) →
  ∀ '(a, t) ∈ zip addrs (map g ts), (g <$> coh) !!! a ≤ t.
Proof using Hp.
  intros Hcoh [a t] Hin. rewrite zip_map_r in Hin.
  apply list_elem_of_fmap in Hin as [[a0 t0] [Heq Hin]]. cbn in Heq. injection Heq as -> ->.
  specialize (Hcoh (a0, t0) Hin). cbn in Hcoh.
  rewrite (VMSwapRemoveMap.lookup_total_map p Hp). apply unshift_mono, Hcoh.
Qed.
End Map.

Section Removed.
Context (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat) (imem : memoryMap).
Local Notation p := (S (length r)).
Local Notation g := (unshift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc epoch).

Lemma read_all_remove addr size l tmin :
  match Memory.read_all addr size imem (l ++ e :: r) tmin,
    Memory.read_all addr size imem (l ++ r) (g tmin) with
  | Ok before, Ok after => after = map (bytes_map g) before
  | Error _, Error _ => True
  | _, _ => False
  end.
Proof.
  pose proof (VMSwapInsert.read_all_remove r tlbi rc epoch imem addr size l tmin) as Hread.
  destruct (Memory.read_all addr size imem (l ++ e :: r) tmin) as [before|err];
    destruct (Memory.read_all addr size imem (l ++ r) (g tmin)) as [after|err']; try contradiction; [|exact I].
  cbn in Hread. subst before. rewrite map_map.
  transitivity (map id after); [symmetry; apply map_id|]. apply map_ext. intro bytes. symmetry. apply bytes_unshift_shift.
Qed.
End Removed.

Section Handlers.
Context (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat) (imem : memoryMap).
Local Notation p := (S (length r)).
Local Notation g := (unshift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc epoch).
Local Notation PR := (VMSwapRemoveLocal.pp_rel r tlbi rc epoch).
Local Notation avoids := (VMSwapRemoveMap.promises_avoid p).
Local Notation inv_ok := (VMSwapRemoveViews.opt_ok (λ t, t ≠ p)).

Definition read_rel (a b : PPState.t TState.t Ev.t IIS.t) :=
  PR a b ∧ avoids (PPState.state a) ∧ inv_ok (IIS.inv_time (PPState.iis a)).
Local Notation R := read_rel.

Lemma get_state : esim R (λ x y, y = ts_map g x ∧ avoids x) (mget PPState.state) (mget PPState.state).
Proof. apply esim_mget. intros a b [[_ [Ht _]] [Hp _]]. split; assumption. Qed.
Lemma get_strict : esim R (λ x y : nat, y = g x)
  (mget (IIS.strict ∘ PPState.iis)) (mget (IIS.strict ∘ PPState.iis)).
Proof. apply esim_mget. intros a b [[_ [_ Hi]] _]. cbn [compose]. rewrite Hi. reflexivity. Qed.
Lemma get_mem : esim R (λ x y, ∃ l, x = l ++ e :: r ∧ y = l ++ r) (mget PPState.mem) (mget PPState.mem).
Proof. apply esim_mget. intros a b [[Hm _] _]. exact Hm. Qed.
Lemma get_inv : esim R (λ x y : option nat, y = g <$> x ∧ inv_ok x)
  (mget (IIS.inv_time ∘ PPState.iis)) (mget (IIS.inv_time ∘ PPState.iis)).
Proof.
  apply esim_mget. intros a b [[_ [_ Hi]] [_ Hinv]]. cbn [compose].
  split; [rewrite Hi; reflexivity|exact Hinv].
Qed.
Lemma set_state f1 f2 : (∀ ts, f2 (ts_map g ts) = ts_map g (f1 ts)) →
  (∀ ts, avoids ts → avoids (f1 ts)) → esim R eq (mset PPState.state f1) (mset PPState.state f2).
Proof.
  intros Hmap Hprom. apply esim_mset. intros [ta ma ia] [tb mb ib] [[Hm [Ht Hi]] [Hp Hinv]].
  unfold read_rel, VMSwapRemoveLocal.pp_rel; cbn in *; subst tb ib.
  split; [split; [exact Hm|split; [apply Hmap|reflexivity]]|split; [apply Hprom, Hp|exact Hinv]].
Qed.
Lemma set_iis f1 f2 : (∀ iis, f2 (iis_map g iis) = iis_map g (f1 iis)) →
  (∀ iis, IIS.inv_time (f1 iis) = IIS.inv_time iis) →
  esim R eq (mset PPState.iis f1) (mset PPState.iis f2).
Proof.
  intros Hmap Hinv. apply esim_mset. intros [ta ma ia] [tb mb ib] [[Hm [Ht Hi]] [Hp Hstamp]].
  unfold read_rel, VMSwapRemoveLocal.pp_rel; cbn in *; subst tb ib.
  split; [split; [exact Hm|split; [reflexivity|apply Hmap]]|split; [exact Hp|rewrite Hinv; exact Hstamp]].
Qed.
Lemma add v : esim R eq (mset PPState.iis (IIS.add v)) (mset PPState.iis (IIS.add (g v))).
Proof. apply set_iis; [intro; symmetry; apply VMSwapRemoveRead.iis_add|intro; reflexivity]. Qed.
Lemma cohs_promises avs ts : avoids ts → avoids (TState.update_cohs avs ts).
Proof.
  intro Hprom. induction avs as [|[a v] avs IH]; [exact Hprom|].
  change (avoids (TState.update_coh a v (TState.update_cohs avs ts))). exact IH.
Qed.

Ltac bind V := eapply (esim_bind _ V); [|
  let x := fresh "x" in let y := fresh "y" in let Hxy := fresh "Hxy" in intros x y Hxy;
  lazymatch type of x with unit => clear Hxy; destruct x, y | _ => idtac end].
Ltac fold_unshift := unfold join, join_nat in *;
  repeat first [rewrite (VMSwapRemoveMap.unshift_view_if p ltac:(lia))|rewrite <- unshift_max].

Theorem read_mem_exact addr size macc :
  esim R eq (read_mem_explicit imem addr size macc) (read_mem_explicit imem addr size macc).
Proof.
  unfold read_mem_explicit.
  bind (λ x y, y = ts_map g x ∧ avoids x); [apply get_state|]. destruct Hxy as [-> Hprom].
  bind (λ x y : nat, y = g x); [apply get_strict|]. subst y.
  eapply esim_bind; [apply esim_guard_discard; apply (VMSwapRemoveMap.map_no_promises_until p ltac:(lia)), Hprom|intros ? ? _].
  cbn [ts_map TState.vrd TState.vwr TState.vdmb TState.vdsb TState.vcse TState.vacq TState.vrel
    TState.vspec TState.fwdb TState.coh].
  rewrite (VMSwapRemoveMap.map_min_cohs p ltac:(lia)). fold_unshift.
  bind (λ x y, ∃ l, x = l ++ e :: r ∧ y = l ++ r); [apply get_mem|].
  destruct Hxy as (l & -> & ->).
  eapply (esim_bind _ (λ x y : list (list (bv 8 * nat)), y = map (bytes_map g) x ∧
    ∀ bytes, bytes ∈ x → Forall (λ bt, bt.2 ≠ p) bytes)).
  { match goal with |- context [Memory.read_all _ _ _ (l ++ e :: r) ?t] =>
      pose proof (read_all_remove r tlbi rc epoch imem addr size l t) as Hread end.
    apply esim_lift_result.
    - intros candidates Hrun. rewrite Hrun in Hread.
      destruct (Memory.read_all _ _ _ (l ++ r) _) as [short|err] eqn:Hshort; [|contradiction].
      exists short. split; [reflexivity|]. split; [exact Hread|].
      eapply VMSwapRemoveTimes.read_all_avoids; exact Hrun.
    - intros err Hrun. rewrite Hrun in Hread.
      destruct (Memory.read_all _ _ _ (l ++ r) _); [contradiction|eauto]. }
  intros candidates candidates' [-> Htimes].
  eapply (esim_bind _ (λ x y : list (bv 8 * nat), y = bytes_map g x ∧ Forall (λ bt, bt.2 ≠ p) x)).
  { split; [|apply eerr_nil; reflexivity].
    intros a b a' bytes Hrel Hrun. apply Exec.elem_of_mchoosel_inv in Hrun as [-> Hin].
    exists b, (bytes_map g bytes). split; [apply Exec.elem_of_mchoosel, list_elem_of_fmap; eauto|].
    split; [exact Hrel|split; [reflexivity|apply Htimes, Hin]]. }
  intros candidate candidate' [-> Hcandidate]. rewrite max_bytes.
  assert (Htime : max_list_with snd candidate ≠ p) by
    (apply VMSwapRemoveTimes.max_list_avoids; [lia|exact Hcandidate]).
  rewrite fwd_bytes_map by (try lia; exact Htime).
  match goal with |- context [map (fb_map g) ?L] => destruct (fb_map_parts g L) as (H1 & H2 & H3) end.
  rewrite H1, H2, H3, foldr_max_map. fold_unshift.
  bind (@eq unit).
  { destruct (is_atomic_rmw macc); [|apply esim_ret; reflexivity].
    apply esim_msetv. intros [ta ma ia] [tb mb ib] [[Hm [Ht Hi]] [Hp Hinv]].
    unfold read_rel, VMSwapRemoveLocal.pp_rel; cbn in *; subst tb ib.
    split; [split; [exact Hm|split; reflexivity]|split; assumption]. }
  eapply esim_bind; [apply esim_guard_discard; apply (coh_guard_map p ltac:(lia))|intros ? ? _].
  bind (λ x y : option nat, y = g <$> x ∧ inv_ok x); [apply get_inv|].
  match goal with H : ?y = g <$> ?x ∧ inv_ok ?x |- _ => destruct H as [-> Hinv] end.
  bind (@eq unit).
  { apply esim_guard_discard'. match goal with |- context [if ?o is Some _ then _ else _] => destruct o as [time|] end;
      cbn; [apply (proj2 (unshift_lt_iff_ne p _ time (Hinv time eq_refl) ltac:(lia)))|auto]. }
  rewrite zip_map_r.
  bind (@eq unit); [apply set_state; [intro; symmetry; apply (VMSwapRemoveMap.map_update_cohs p ltac:(lia))|apply cohs_promises]|].
  bind (@eq unit); [apply set_state; [intro; symmetry; apply (VMSwapRemoveMap.map_vrd p ltac:(lia))|intros; assumption]|].
  bind (@eq unit); [apply set_state; [intro; symmetry; apply (VMSwapRemoveMap.map_vacq p ltac:(lia))|intros; assumption]|].
  bind (@eq unit); [apply set_state; [intro; symmetry; apply (VMSwapRemoveMap.map_vspec p ltac:(lia))|intros; assumption]|].
  bind (@eq unit).
  { destruct (is_exclusive macc); [|apply esim_ret; reflexivity].
    apply set_state; [intro; symmetry; apply (VMSwapRemoveMap.map_set_xclb p ltac:(lia))|intros; assumption]. }
  bind (@eq unit); [apply add|apply esim_ret; reflexivity].
Qed.
Theorem read_mem_sim addr size macc a b : VMSwapRemoveLocal.related r tlbi rc epoch a b →
  avoids (PPState.state a) → inv_ok (IIS.inv_time (PPState.iis a)) →
  VMSwapInsert.esim_at (VMSwapRemoveLocal.related r tlbi rc epoch) eq
    (read_mem_explicit imem addr size macc) (read_mem_explicit imem addr size macc) a b.
Proof.
  intros Hrel Hprom Hinv. destruct (related_factor r tlbi rc epoch a b Hrel) as [mid [Hmap Hcache]].
  assert (Hread : read_rel a mid) by (split; [exact Hmap|split; assumption]).
  pose proof (read_mem_exact addr size macc) as [Mr Me].
  pose proof (VMCacheSimOutcome.read_mem_explicit_sim imem addr size macc) as [Cr Ce].
  split.
  - intros a' x Hrun. destruct (Mr a mid a' x Hread Hrun) as (mid' & y & Hrun' & [Hmap' _] & <-).
    destruct (Cr mid b mid' x Hcache Hrun') as (b' & y & Hrun'' & Hcache' & <-).
    exists b', x. split; [exact Hrun''|]. split; [eapply related_compose; eassumption|reflexivity].
  - intros a' err Hrun. destruct (Me a mid a' err Hread Hrun) as (mid' & err' & Hrun' & [Hmap' _]).
    destruct (Ce mid b mid' err' Hcache Hrun') as (b' & err'' & Hrun'' & Hcache').
    exists b', err''. split; [exact Hrun''|eapply related_compose; eassumption].
Qed.
End Handlers.
End VMSwapRemoveLoad.
