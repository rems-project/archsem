(******************************************************************************)
(* Timestamp maps that fix a bounded thread state                             *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews PromiseFirstSailVMCacheState
  PromiseFirstSailVMCacheOrder PromiseFirstSailVMCacheExchange PromiseFirstSailVMBBMTransport
  PromiseFirstSailVMInstructionReplay PromiseFirstSailVMCacheRefill PromiseFirstSailVMCacheSim
  PromiseFirstSailVMSwapSim PromiseFirstSailVMSwapLookup
  PromiseFirstSailVMSwapRemoveInit.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapFixed.
Import VMPromising VMSwapSim VMSwapLookup.
#[local] Typeclasses Transparent Memory.t view UMPromising.view.
Section Fixed.
Context (f : nat → nat) (bound : nat).
Hypothesis Hfix : ∀ t, t ≤ bound → f t = t.
Set Default Proof Using "All".

Lemma vatlb_fixed c : VMCacheOrder.good bound c → VMCacheExchange.unique_entries c →
  vatlb_map f (TLB.vatlb c) = TLB.vatlb c.
Proof.
  intros Hgood Hunique. apply vatlb_ext. intro lvl. unfold vatlb_map. rewrite hget_hmap.
  unfold TLB.VATLB.T. apply map_eq. intro nd. rewrite lookup_fmap.
  destruct (hget lvl (TLB.vatlb c) !! nd) as [entries|] eqn:Hentries;
    rewrite Hentries; cbn; [|reflexivity].
  f_equal. apply VMSwapRemoveInit.list_fixed, Forall_forall. intros [entry evs] Hin. cbn.
  assert (Hhistory : VMCacheRefill.history c (existT (existT lvl nd) entry) = evs).
  { apply VMBBMTransport.row_history; [exact Hunique|].
    change ((entry, evs) ∈ default [] (hget lvl (TLB.vatlb c) !! nd)). rewrite Hentries.
    apply list_elem_of_In. exact Hin. }
  pose proof (proj2 (Hgood (existT (existT lvl nd) entry))) as Hbound.
  rewrite Hhistory in Hbound. f_equal. unfold map_evs. apply VMSwapRemoveInit.list_fixed.
  eapply list.Forall_impl; [exact Hbound|]. intros [event time] Htime. cbn in *. rewrite Hfix by exact Htime. reflexivity.
Qed.

Lemma cache_fixed c : VMCacheState.cache_inv bound c → VMRoots.rbound bound c → tlb_map f c = c.
Proof.
  intros [Hgood [Hunique Hvalid]] Hroots.
  assert (Hvatlb : vatlb_map f (TLB.vatlb c) = TLB.vatlb c) by (apply vatlb_fixed; assumption).
  assert (Hrootmap : map (λ rt, (rt.1, f rt.2)) (TLB.asid_roots c) = TLB.asid_roots c).
  { apply VMSwapRemoveInit.list_fixed. eapply list.Forall_impl; [exact Hroots|].
    intros [root time] Htime. cbn in *. rewrite Hfix by exact Htime. reflexivity. }
  unfold tlb_map. rewrite Hvatlb, Hrootmap. destruct c. reflexivity.
Qed.

Theorem thread_fixed ts : VMViews.ts_ok bound ts → VMRoots.roots_ok bound ts → ts_map f ts = ts.
Proof.
  intros Hbounds Hroots.
  pose proof (VMSwapRemoveInit.ts_frame_fixed f bound Hfix ts Hbounds) as Hframe.
  assert (Hcache : TState.tlb (ts_map f ts) = TState.tlb ts).
  { rewrite ts_map_tlb. destruct (TState.tlb ts) as [c|] eqn:Hc; cbn; [|reflexivity].
    f_equal. apply cache_fixed; [apply (VMViews.ok_cache _ _ Hbounds c Hc)|].
    unfold VMRoots.roots_ok in Hroots. rewrite Hc in Hroots. exact Hroots. }
  rewrite <- Hcache in Hframe. rewrite VMCacheSim.setv_tlb_same in Hframe. exact Hframe.
Qed.
End Fixed.
End VMSwapFixed.
