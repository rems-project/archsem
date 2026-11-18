(******************************************************************************)
(* Invalid root translations under the lookup bounds after an actual promise *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstSailRead PromiseFirstSailVMLookup
  PromiseFirstSailVMInterval PromiseFirstSailVMGuards PromiseFirstSailVMCacheFill.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMRootLookupReplay.
Import VMPromising VMIntervalReplay.

Lemma read_all_prefix {E} (get_msg : E → option Msg.t) addr size imem
    prefix mem tmin candidates :
  tmin ≤ length mem →
  PromMemory.read_all get_msg addr size imem mem tmin = Ok candidates →
  ∃ candidates',
    PromMemory.read_all get_msg addr size imem (prefix ++ mem)%list tmin = Ok candidates' ∧
    ∀ candidate, candidate ∈ candidates → candidate ∈ candidates'.
Proof.
  intros Hmin Hread. induction prefix as [|ev prefix IH]; cbn [app].
  - exists candidates. auto.
  - destruct IH as [middle [Hmiddle Hsubset]].
    destruct (read_all_cons_preserves_candidates get_msg addr size imem
      (prefix ++ mem)%list ev tmin middle ltac:(rewrite length_app; lia) Hmiddle)
      as [final [Hfinal Hsubset']].
    exists final. split; [exact Hfinal|]. intros candidate Hin. auto.
Qed.

Lemma cut_before_length {E} time (mem : list E) :
  time ≤ length mem → length (PromMemory.cut_before time mem) = time.
Proof. unfold PromMemory.cut_before. rewrite length_drop. lia. Qed.

Lemma cut_before_widen {E} low high (mem : list E) :
  low ≤ high → high ≤ length mem →
  ∃ extra, PromMemory.cut_before high mem =
    (extra ++ PromMemory.cut_before low mem)%list.
Proof.
  intros Hlow Hhigh.
  exists (take (high - low) (PromMemory.cut_before high mem)).
  assert (Hdrop : drop (high - low) (PromMemory.cut_before high mem) =
    PromMemory.cut_before low mem).
  { unfold PromMemory.cut_before. rewrite drop_drop. f_equal. lia. }
  rewrite <- Hdrop. symmetry. apply take_drop.
Qed.

Lemma read_all_btw_widen {E} (get_msg : E → option Msg.t) addr size imem mem
    tmin tmax tmax' candidates :
  tmin ≤ tmax → tmax ≤ tmax' → tmax' ≤ length mem →
  PromMemory.read_all_btw get_msg addr size imem mem tmin tmax = Ok candidates →
  ∃ candidates',
    PromMemory.read_all_btw get_msg addr size imem mem tmin tmax' = Ok candidates' ∧
    ∀ candidate, candidate ∈ candidates → candidate ∈ candidates'.
Proof.
  intros Hmin Hmax Hbound. unfold PromMemory.read_all_btw.
  rewrite !decide_True by lia. intro Hread.
  pose proof (cut_before_length tmax mem ltac:(lia)) as Hlen.
  pose proof (cut_before_length tmax' mem Hbound) as Hlen'.
  destruct (cut_before_widen tmax tmax' mem Hmax Hbound) as [extra Hextra].
  assert (Hread0 : PromMemory.read_all get_msg addr size imem
    (PromMemory.cut_before tmax mem) tmin = Ok candidates).
  { unfold PromMemory.read_all. rewrite Hlen. exact Hread. }
  destruct (read_all_prefix get_msg addr size imem extra _ tmin candidates
    ltac:(rewrite Hlen; exact Hmin) Hread0) as [candidates' [Hread' Hin]].
  exists candidates'. split; [|exact Hin].
  rewrite <- Hextra in Hread'. unfold PromMemory.read_all in Hread'.
  rewrite Hlen' in Hread'. exact Hread'.
Qed.

Lemma read_all_pte_larger_bound addr imem mem event tmin tmax tmax' ptes :
  tmin ≤ tmax → tmax ≤ length mem → tmax ≤ tmax' → tmax' ≤ S (length mem) →
  Memory.read_all_pte addr imem mem tmin tmax = Ok ptes →
  ∃ ptes', Memory.read_all_pte addr imem (event :: mem) tmin tmax' = Ok ptes' ∧
    ∀ pte, pte ∈ ptes → pte ∈ ptes'.
Proof.
  intros Hmin Hbound Hmax Hbound' Hread.
  rewrite <- (VMLookupReplay.read_all_pte_future addr imem mem event tmin tmax Hbound) in Hread.
  unfold Memory.read_all_pte in Hread |- *.
  destruct (Memory.read_all_btw addr 8 imem (event :: mem) tmin tmax)
    as [bytes|err] eqn:Hbytes; [|discriminate].
  injection Hread as <-.
  destruct (read_all_btw_widen Ev.get_msg addr 8 imem (event :: mem)
    tmin tmax tmax' bytes Hmin Hmax Hbound' Hbytes) as [bytes' [Hbytes' Hsubset]].
  exists (map (λ bs, (bv_of_bytes 64 bs.*1, max_list_with snd bs)) bytes').
  split; [unfold Memory.read_all_btw; rewrite Hbytes'; reflexivity|].
  intros pte Hin. apply list_elem_of_fmap in Hin as [bs [-> Hin]].
  apply list_elem_of_fmap. exists bs. auto.
Qed.

(** The level-zero invalid-descriptor branch of the production lookup. *)
Definition root_lookup imem mem (ts : TState.t) (upper : bool) vpn ttbr0 tmin_unc tmax :
    Exec.res string TLB.Result.t :=
  if decide (tmin_unc ≤ tmax) then
    ttbrs ← mlift
      (if upper then
        othrow "Can't read TTBR1_EL1, but using negative addresses" $
          TState.read_sreg_indirect ts TTBR1_EL1 : result string (list (bv 64 * view))
       else mret [(ttbr0, 0)]);
    '(ttbr, vttbr) ← mchoosel ttbrs;
    let pte_addr := index_table (ttbr_root_table ttbr) (vpn_level_index 0%fin vpn) in
    let tmin := tmin_unc ⊔ vttbr in
    ptes ← mlift $ Memory.read_all_pte pte_addr imem mem tmin tmax;
    mchoosel (map (λ '(pte, vpte), TLB.Result.make ttbr [pte] (tmin ⊔ vpte) tmax None)
      (filter (λ '(pte, _), ¬ is_tlb_fillable 0%fin pte) ptes))
  else mdiscard.

Lemma root_lookup_larger_bound imem mem event ts ts' upper vpn ttbr0
    tmin_unc tmax tmax' result :
  TState.read_sreg_indirect ts' TTBR1_EL1 = TState.read_sreg_indirect ts TTBR1_EL1 →
  tmax ≤ length mem → tmax ≤ tmax' → tmax' ≤ S (length mem) →
  Exec.elem_of_results result (root_lookup imem mem ts upper vpn ttbr0 tmin_unc tmax) →
  ∃ result',
    Exec.elem_of_results result'
      (root_lookup imem (event :: mem) ts' upper vpn ttbr0 tmin_unc tmax') ∧
    extends_translation (length mem) result result'.
Proof.
  intros Hsreg Hbound Hmax Hbound'. unfold root_lookup. rewrite Hsreg.
  destruct (decide (tmin_unc ≤ tmax)) as [Hrange|Hempty];
    [|intro H; inversion H].
  rewrite decide_True by lia. intro Hin.
  apply Exec.elem_of_res_bind_elim in Hin as [ttbrs [Hregs Hin]].
  apply Exec.elem_of_res_bind_elim in Hin as [[ttbr vttbr] [Hchoice Hin]].
  apply Exec.elem_of_res_bind_elim in Hin as [ptes [Hread Hin]].
  apply PromiseFirstCurrent.lift_result_res_success in Hread.
  apply Exec.elem_of_res_mchoosel_inv in Hin.
  apply list_elem_of_fmap in Hin as [[pte vpte] [-> Hin]].
  apply list_elem_of_filter in Hin as [Hinvalid Hin].
  assert (Hmin : tmin_unc ⊔ vttbr ≤ tmax).
  { destruct (decide (tmin_unc ⊔ vttbr ≤ tmax)); [assumption|].
    unfold Memory.read_all_pte, Memory.read_all_btw, PromMemory.read_all_btw in Hread.
    rewrite decide_False in Hread by assumption.
    injection Hread as <-. inversion Hin. }
  destruct (read_all_pte_larger_bound _ imem mem event _ tmax tmax' ptes
    Hmin Hbound Hmax Hbound' Hread) as [ptes' [Hread' Hsubset]].
  exists (TLB.Result.make ttbr [pte] (tmin_unc ⊔ vttbr ⊔ vpte) tmax' None).
  split.
  - eapply Exec.elem_of_res_bind_intro; [exact Hregs|].
    eapply Exec.elem_of_res_bind_intro; [exact Hchoice|].
    eapply Exec.elem_of_res_bind_intro with (a := ptes').
    + apply PromiseFirstCurrent.lift_result_res_success. exact Hread'.
    + apply Exec.elem_of_res_mchoosel, list_elem_of_fmap.
      exists (pte, vpte). split; [reflexivity|]. apply list_elem_of_filter. auto.
  - apply extends_translation_make, Hmax.
Qed.

(** Emit an actual promise and use the new bound computed by run_trans_start.
    Invalid root descriptors are uncached alternatives of TState.tlb_lookup. *)
Theorem emit_promise_root_lookup tid imem mem event ts issued old ifetch upper vpn
    asid ttbr0 tmin_ok tmin_unc result :
  TState.emit_promise tid imem (event :: mem) event ts = Ok issued →
  TState.tlb ts = Some old →
  Exec.elem_of_results result (root_lookup imem mem ts upper vpn ttbr0 tmin_unc
    (pred (TState.min_promise (length mem) ts))) →
  ∃ result',
    Exec.elem_of_results result'
      (TState.tlb_lookup tid imem (event :: mem) issued ifetch upper vpn asid ttbr0
        tmin_ok tmin_unc (pred (TState.min_promise (length (event :: mem)) issued))) ∧
    extends_translation (length mem) result result'.
Proof.
  intros Hpromise Hcache Hlookup.
  destruct (VMCacheFillReplay.emit_promise_cache_extends tid imem mem event
    ts issued old Hcache Hpromise) as [new [Hnew _]].
  pose proof (VMGuardReplay.min_promise_bound (length mem) ts) as Hbound.
  pose proof (VMGuardReplay.min_promise_bound (length (event :: mem)) issued) as Hbound'.
  pose proof (VMGuardReplay.emit_promise_translation_bound tid imem mem event
    ts issued Hpromise) as Hgrowth.
  destruct (root_lookup_larger_bound imem mem event ts issued upper vpn ttbr0
    tmin_unc (pred (TState.min_promise (length mem) ts))
    (pred (TState.min_promise (length (event :: mem)) issued)) result
    (VMLookupReplay.emit_promise_preserves_sreg tid imem (event :: mem) event
      ts issued TTBR1_EL1 Hpromise) ltac:(lia) Hgrowth ltac:(cbn [length] in Hbound' |- *; lia)
    Hlookup) as [result' [Hin Hsame]].
  exists result'. split; [|exact Hsame].
  unfold TState.tlb_lookup. rewrite Hnew.
  unfold Exec.elem_of_results, Exec.merge. cbn [Exec.results].
  apply elem_of_app. right. exact Hin.
Qed.
End VMRootLookupReplay.
