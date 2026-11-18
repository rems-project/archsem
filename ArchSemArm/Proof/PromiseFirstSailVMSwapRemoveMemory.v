(******************************************************************************)
(* Dependency-view exclusion through explicit memory reads                   *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews PromiseFirstSailVMSwapRemoveState
  PromiseFirstSailVMSwapRemoveViews PromiseFirstSailVMSwapRemoveThread PromiseFirstSailVMSwapRemoveTimes.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveMemory.
Import VMPromising VMSwapRemoveState VMSwapRemoveViews VMSwapRemoveThread.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

#[local] Hint Rewrite VMViews.strict_set_rmw_read VMViews.strict_set_trs
  VMViews.state_set_state VMViews.mem_set_state VMViews.iis_set_state
  VMViews.state_set_iis VMViews.mem_set_iis VMViews.iis_set_iis
  VMViews.state_set_state_field VMViews.mem_set_state_field VMViews.iis_set_state_field
  VMViews.state_set_iis_field VMViews.mem_set_iis_field VMViews.iis_set_iis_field : pp_remove_memory.
Ltac simpl_pp := unfold ok, setv in *; autorewrite with pp_remove_memory in *;
  cbn [PPState.state PPState.mem PPState.iis fst snd] in *.
Ltac solve_view :=
  cbn [compose PPState.state PPState.iis fst snd];
  first [assumption | apply allowed_max; solve_view | apply allowed_zero; lia
    | apply view_if_ok; [apply allowed_zero; lia|solve_view]].
Ltac solve_fields :=
  first [assumption
    | apply update_vrd; [apply allowed_max|solve_view|solve_fields]
    | apply update_vacq; [apply allowed_max|solve_view|solve_fields]
    | apply update_vspec; [apply allowed_max|solve_view|solve_fields]
    | apply update_cohs; [apply allowed_zero; lia|apply allowed_max|assumption|solve_fields]
    | apply set_xclb; [solve_view|solve_view|solve_fields]
    | apply iis_add; [apply allowed_max|solve_view|solve_fields]
    | apply iis_rmw_read; [intros ? ? H; injection H as <- <-; solve_view|solve_fields]].

Lemma update_cohs_frame avs ts : TState.vcse (TState.update_cohs avs ts) = TState.vcse ts ∧
  TState.tlb (TState.update_cohs avs ts) = TState.tlb ts.
Proof. induction avs as [|[a v] avs IH]; [split; reflexivity|exact IH]. Qed.

Ltac cohs_frame ts :=
  match goal with |- context[TState.update_cohs ?avs ts] =>
    first [change (TState.vcse (TState.update_cohs avs ts) = TState.vcse ts); apply (proj1 (update_cohs_frame avs ts))
      |change (TState.tlb (TState.update_cohs avs ts) = TState.tlb ts); apply (proj2 (update_cohs_frame avs ts))]
  end.

Lemma read_mem_explicit_ok imem l r tlbi rc epoch addr size macc pp pp' value :
  PPState.mem pp = l ++ Ev.Tlbi tlbi rc epoch :: r → ok (S (length r)) pp →
  Exec.elem_of_results (pp', value) (read_mem_explicit imem addr size macc pp) → ok (S (length r)) pp'.
Proof.
  destruct pp as [ts mem iis]. cbn. intros -> Hok Hrun. unfold read_mem_explicit in Hrun.
  VMViews.invert; subst; simpl_pp.
  all: pose proof Hok as [[Hts Hcache] Hiis]; VMViews.facts Hts; VMViews.facts Hiis.
  all: match goal with H : Memory.read_all _ _ _ _ _ = Ok _, Hin : ?candidate ∈ _ |- _ =>
    assert (Hcand : Forall (λ byte, allowed (S (length r)) (TState.vcse ts) byte.2) candidate) by
      (pose proof (VMSwapRemoveTimes.read_all_avoids _ _ _ _ _ _ _ _ _ _ H _ Hin) as Htimes;
       eapply list.Forall_impl; [exact Htimes|]; intros byte Hne; left; exact Hne) end.
  all: pose proof (max_list_ok _ (allowed_zero (S (length r)) (TState.vcse ts) ltac:(lia))
    (allowed_max _ _) snd _ Hcand) as Htread.
  all: match goal with |- context[map ?f (zip ?addrs ?candidate)] =>
    destruct (mapped_views (allowed (S (length r)) (TState.vcse ts)) f addrs candidate)
      as [Hviews Htimes]; [|exact Hcand|] end.
  all: try (intros [a [byte twrite]] Hb; cbn in Hb |- *;
    match goal with |- context[default _ ?o] => destruct o eqn:Hfwd end; cbn;
    [eapply read_fwd_ok; [apply allowed_max|exact ok_fwdb0|exact Hfwd]|split; assumption]).
  all: match goal with |- context[foldr Init.Nat.max 0 ?xs] =>
    pose proof (foldr_max_ok _ (allowed_zero (S (length r)) (TState.vcse ts) ltac:(lia))
      (allowed_max _ _) xs Hviews) as Hreads end.
  all: cbn in Hreads.
  all: apply (VMViews.zip_Forall_snd _ (addr_range addr size)) in Htimes.
  all: eapply (frame (S (length r)) ts _ iis); [cohs_frame ts|cohs_frame ts|solve_fields|solve_fields|exact Hok].
Qed.
End VMSwapRemoveMemory.
