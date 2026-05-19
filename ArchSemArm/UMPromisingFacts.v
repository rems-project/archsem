(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
(*      Shreeka Lohani, University of Cambridge                               *)
(*      Zongyuan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
(*                                                                            *)
(*  Redistribution and use in source and binary forms, with or without        *)
(*  modification, are permitted provided that the following conditions        *)
(*  are met:                                                                  *)
(*                                                                            *)
(*   1. Redistributions of source code must retain the above copyright        *)
(*      notice, this list of conditions and the following disclaimer.         *)
(*                                                                            *)
(*   2. Redistributions in binary form must reproduce the above copyright     *)
(*      notice, this list of conditions and the following disclaimer in the   *)
(*      documentation and/or other materials provided with the distribution.  *)
(*                                                                            *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS       *)
(*  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT         *)
(*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS         *)
(*  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE            *)
(*  COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,      *)
(*  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,      *)
(*  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS     *)
(*  OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND    *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR     *)
(*  TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE    *)
(*  USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.  *)
(*                                                                            *)
(******************************************************************************)

From ASCommon Require Import Options.
From ASCommon Require Import Common Exec FMon StateT.

From ArchSem Require Import GenPromising.
Require Import ArmInst UMPromising.

#[local] Open Scope stdpp.

Import Promising.

#[local] Typeclasses Transparent Memory.t.

Lemma TState_reg_map_promise v ts :
  TState.reg_map (TState.promise v ts) = TState.reg_map ts.
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma UMPromising_promise_tid_reg_map {n} (tid_p tid : fin n)
    (msg : Msg.t) (st : CPState.t TState.t Msg.t n) :
  TState.reg_map
    (CPState.tstate tid
       (CPState.promise_tid UMPromising tid_p msg st)) =
  TState.reg_map (CPState.tstate tid st).
Proof.
  destruct st as [tstates initmem events].
  unfold CPState.promise_tid, CPState.tstate.
  cbn.
  destruct (decide (tid = tid_p)) as [->|Hne].
  - autorewrite with vec.
    apply TState_reg_map_promise.
  - unfold alter.
    cbn.
    rewrite vlookup_insert_ne by congruence.
    reflexivity.
Qed.

Lemma UMPromising_terminated_tid_promise {n}
    (term : terminationCondition n) (tid_p tid : fin n)
    (msg : Msg.t) (st : CPState.t TState.t Msg.t n) :
  CPState.terminated_tid UMPromising term
    (CPState.promise_tid UMPromising tid_p msg st) tid =
  CPState.terminated_tid UMPromising term st tid.
Proof.
  unfold CPState.terminated_tid.
  cbn.
  rewrite UMPromising_promise_tid_reg_map.
  reflexivity.
Qed.

Definition outcome_future_promise_stable_promised tid initmem
    (msg : Msg.t) (out : outcome) : Prop :=
  ∀ ppst ppst' (eret : eff_ret out),
    Exec.elem_of_results (ppst', eret)
      ((run_outcome tid initmem out |$> fst) ppst) →
    Exec.elem_of_results
      (CPState.promise_ppstate UMPromising tid initmem msg ppst', eret)
      ((run_outcome tid initmem out |$> fst)
         (CPState.promise_ppstate UMPromising tid initmem msg ppst)).

Fixpoint imon_future_promise_stable_promised tid initmem
    (msg : Msg.t) A (mon : iMon A) : Prop :=
  match mon with
  | Ret _ => True
  | Next call k =>
      match call with
      | inl out =>
          outcome_future_promise_stable_promised tid initmem msg out ∧
          ∀ eret,
            imon_future_promise_stable_promised tid initmem msg A (k eret)
      | inr _ =>
          ∀ ret,
            imon_future_promise_stable_promised tid initmem msg A (k ret)
      end
  end.

Lemma mem_read_outcome_future_promise_stable_promised tid initmem code msg
    addr size macc addr_space :
  (is_ifetch macc = true →
    event_misses_code code msg ∧ ifetch_in_code code addr size) →
  (∀ ppst,
    is_ifetch macc = false →
    is_explicit macc = true →
    ppstate_read_times_le macc ppst) →
  outcome_future_promise_stable_promised tid initmem msg
    (MemRead (MemReq.make macc addr addr_space size 0)).
Proof.
  intros Hifetch_assume Hread_bound ppst ppst' eret Hrun.
  unfold CPState.promise_ppstate, UMPromising.
  cbn.
  eapply run_outcome_mem_read_promise_cons_old_fmap.
  - exact Hifetch_assume.
  - intros Hifetch Hexplicit.
    apply Hread_bound; assumption.
  - exact Hrun.
Qed.

Lemma reg_read_outcome_promise_state_fmap tid initmem reg racc
    ppst ppst' p mem_new eret :
  Exec.elem_of_results (ppst', eret)
    ((run_outcome tid initmem (RegRead reg racc) |$> fst) ppst) →
  Exec.elem_of_results
    (PPState.Make (TState.promise p (PPState.state ppst'))
       mem_new (PPState.iis ppst'), eret)
    ((run_outcome tid initmem (RegRead reg racc) |$> fst)
       (PPState.Make (TState.promise p (PPState.state ppst))
          mem_new (PPState.iis ppst))).
Proof.
  intro Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hrun]].
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_guard [p_racc [Hguard Hrun]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hguard) as Hracc.
  apply Exec.elem_of_guard_or_inv in Hguard as ->.
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_ts [ts [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_reg [[val view] [Hreg Hrun]]].
  unfold othrow in Hreg.
  destruct (dmap_lookup reg (TState.regs (PPState.state ppst)))
    as [[val0 view0]|] eqn:Hlookup.
  2: {
    unfold elem_of, Exec.elem_of_results in Hreg.
    cbn in Hreg.
    inversion Hreg.
  }
  apply Exec.elem_of_mret_inv in Hreg as [-> Hreg].
  inversion Hreg; subst val0 view0.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_iis [[] [Hiis Hrun]]].
  apply Exec.elem_of_mset_inv in Hiis as ->.
  apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
  inversion Heq; subst ppst'.
  inversion Hret; subst eret0 vpre_opt.
  destruct (Exec.elem_of_guard_or
    (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
    (P:=racc = None)
    (PPState.Make (TState.promise p (PPState.state ppst))
       mem_new (PPState.iis ppst))
    "Non trivial reg access types unsupported" Hracc) as
    [p_racc' Hguard'].
  assert
    (Hfull :
       Exec.elem_of_results
         (PPState.Make
            (TState.promise p (PPState.state ppst))
            mem_new (IIS.add view (PPState.iis ppst)),
          (val, None))
         (run_outcome tid initmem (RegRead reg racc)
            (PPState.Make (TState.promise p (PPState.state ppst))
               mem_new (PPState.iis ppst)))).
  {
    simp run_outcome.
    eapply Exec.elem_of_bind_intro with
      (e := guard_or "Non trivial reg access types unsupported"
              (racc = None))
      (st' := PPState.Make (TState.promise p (PPState.state ppst))
                mem_new (PPState.iis ppst))
      (a := p_racc').
    - exact Hguard'.
    - cbn.
      eapply Exec.elem_of_bind_intro with
        (e := (mget PPState.state :
                 Exec.t (PPState.t TState.t Msg.t IIS.t) string TState.t))
        (st' := PPState.Make (TState.promise p (PPState.state ppst))
                  mem_new (PPState.iis ppst))
        (a := TState.promise p (PPState.state ppst)).
      + apply (Exec.elem_of_mget (E:=string)
          (PPState.Make (TState.promise p (PPState.state ppst))
             mem_new (PPState.iis ppst)) PPState.state).
      + cbn.
        rewrite Hlookup.
        eapply Exec.elem_of_bind_intro with
          (st' := PPState.Make (TState.promise p (PPState.state ppst))
                    mem_new (PPState.iis ppst))
          (a := (val, view)).
        * apply Exec.elem_of_mret.
        * cbn.
          eapply Exec.elem_of_bind_intro with
            (st' := PPState.Make (TState.promise p (PPState.state ppst))
                      mem_new (IIS.add view (PPState.iis ppst)))
            (a := ()).
          -- change
               (PPState.Make (TState.promise p (PPState.state ppst))
                  mem_new (IIS.add view (PPState.iis ppst)))
               with
               (set PPState.iis (IIS.add view)
                  (PPState.Make (TState.promise p (PPState.state ppst))
                     mem_new (PPState.iis ppst))).
             apply Exec.elem_of_mset.
          -- cbn.
             apply Exec.elem_of_mret.
  }
  unfold elem_of, Exec.elem_of_results.
  unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  cbn in Hfull |- *.
  set_unfold.
  eapply elem_of_list_fmap_1_alt.
  - exact Hfull.
  - reflexivity.
Qed.

Lemma reg_read_outcome_future_promise_stable_promised tid initmem msg
    reg racc :
  outcome_future_promise_stable_promised tid initmem msg
    (RegRead reg racc).
Proof.
  intros ppst ppst' eret Hrun.
  assert (Hmem : PPState.mem ppst' = PPState.mem ppst).
  {
    apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
    simp run_outcome in Hraw.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_guard [p_racc [Hguard Hraw]]].
    apply Exec.elem_of_guard_or_inv in Hguard as ->.
    cbn in Hraw.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_ts [ts [Hget Hraw]]].
    apply Exec.elem_of_mget_inv in Hget as [-> ->].
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_reg [[val view] [Hreg Hraw]]].
    unfold othrow in Hreg.
    destruct (dmap_lookup reg (TState.regs (PPState.state ppst)))
      as [[val0 view0]|] eqn:Hlookup.
    2: {
      unfold elem_of, Exec.elem_of_results in Hreg.
      cbn in Hreg.
      inversion Hreg.
    }
    apply Exec.elem_of_mret_inv in Hreg as [-> Hreg].
    inversion Hreg; subst val0 view0.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_iis [[] [Hiis Hraw]]].
    apply Exec.elem_of_mset_inv in Hiis as ->.
    apply Exec.elem_of_mret_inv in Hraw as [Heq Hret].
    inversion Heq; subst ppst'.
    reflexivity.
  }
  unfold CPState.promise_ppstate, UMPromising.
  cbn.
  rewrite Hmem.
  eapply reg_read_outcome_promise_state_fmap.
  exact Hrun.
Qed.

Lemma msetv_ppstate_state_result ts
    (ppst : PPState.t TState.t Msg.t IIS.t) :
  Exec.elem_of_results (setv PPState.state ts ppst, ())
    ((msetv PPState.state ts :
        Exec.t (PPState.t TState.t Msg.t IIS.t) string unit) ppst).
Proof.
  unfold msetv, setv.
  apply Exec.elem_of_mset.
Qed.

Lemma reg_write_outcome_promise_state_fmap tid initmem reg racc val
    ppst ppst' p mem_new eret :
  Exec.elem_of_results (ppst', eret)
    ((run_outcome tid initmem (RegWrite reg racc val) |$> fst) ppst) →
  Exec.elem_of_results
    (PPState.Make (TState.promise p (PPState.state ppst'))
       mem_new (PPState.iis ppst'), eret)
    ((run_outcome tid initmem (RegWrite reg racc val) |$> fst)
       (PPState.Make (TState.promise p (PPState.state ppst))
          mem_new (PPState.iis ppst))).
Proof.
  intro Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hrun]].
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_guard [p_racc [Hguard Hrun]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hguard) as Hracc.
  apply Exec.elem_of_guard_or_inv in Hguard as ->.
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_vreg [vreg [Hvreg Hrun]]].
  apply Exec.elem_of_mget_inv in Hvreg as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_vreg' [vreg' [Hvreg' Hrun]]].
  destruct (reg =? pc_reg) eqn:Hpc.
  - apply Exec.elem_of_bind_elim in Hvreg' as
      [pp_vcap [[] [Hvcap Hvreg']]].
    apply Exec.elem_of_mset_inv in Hvcap as ->.
    apply Exec.elem_of_mret_inv in Hvreg' as [-> Hvreg'].
    inversion Hvreg'; subst vreg'.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_ts [ts [Hget Hrun]]].
    apply Exec.elem_of_mget_inv in Hget as [-> ->].
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_nts [nts [Hsetreg Hrun]]].
    unfold othrow in Hsetreg.
    cbn in Hsetreg.
    change
      (PPState.state
         (set PPState.state
            (TState.update TState.vcap (IIS.strict (PPState.iis ppst)))
            ppst))
      with
      (TState.update TState.vcap (IIS.strict (PPState.iis ppst))
         (PPState.state ppst)) in Hsetreg.
    destruct
      (TState.set_reg reg (val, 0%nat)
         (TState.update TState.vcap (IIS.strict (PPState.iis ppst))
            (PPState.state ppst))) as [nts0|] eqn:Hsetreg_eq.
    + rewrite Hsetreg_eq in Hsetreg.
      cbn in Hsetreg.
      apply Exec.elem_of_mret_inv in Hsetreg as [-> Hsetreg].
      inversion Hsetreg; subst nts0.
      apply Exec.elem_of_bind_elim in Hrun as
        [pp_set [[] [Hset Hrun]]].
      unfold msetv in Hset.
      apply Exec.elem_of_mSet_inv in Hset as ->.
      apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
      inversion Heq; subst ppst'.
      inversion Hret; subst eret0 vpre_opt.
      destruct (Exec.elem_of_guard_or
        (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
        (P:=racc = None)
        (PPState.Make (TState.promise p (PPState.state ppst))
           mem_new (PPState.iis ppst))
        "Non trivial reg access types unsupported" Hracc) as
        [p_racc' Hguard'].
      assert
        (Hfull :
           Exec.elem_of_results
             (PPState.Make (TState.promise p nts)
                mem_new (PPState.iis ppst), ((), None))
             (run_outcome tid initmem (RegWrite reg racc val)
                (PPState.Make (TState.promise p (PPState.state ppst))
                   mem_new (PPState.iis ppst)))).
      {
        simp run_outcome.
        eapply Exec.elem_of_bind_intro with
          (st' := PPState.Make (TState.promise p (PPState.state ppst))
                    mem_new (PPState.iis ppst))
          (a := p_racc').
        - exact Hguard'.
        - cbn.
          eapply Exec.elem_of_bind_intro with
            (st' := PPState.Make (TState.promise p (PPState.state ppst))
                      mem_new (PPState.iis ppst))
            (a := IIS.strict (PPState.iis ppst)).
          + apply (Exec.elem_of_mget (E:=string)
              (PPState.Make (TState.promise p (PPState.state ppst))
                 mem_new (PPState.iis ppst)) (IIS.strict ∘ PPState.iis)).
          + cbn.
            rewrite Hpc.
            set (pp_prom :=
              PPState.Make (TState.promise p (PPState.state ppst))
                mem_new (PPState.iis ppst)).
            set (pp_vcap :=
              set PPState.state
                (TState.update TState.vcap (IIS.strict (PPState.iis ppst)))
                pp_prom).
            eapply Exec.elem_of_bind_intro
              with (st' := pp_vcap) (a := 0%nat).
            * eapply Exec.elem_of_bind_intro
                with (st' := pp_vcap) (a := ()).
              -- subst pp_vcap.
                 apply Exec.elem_of_mset.
              -- cbn.
                 apply Exec.elem_of_mret.
            * subst pp_vcap pp_prom.
              cbn.
              eapply Exec.elem_of_bind_intro with
                (st' := PPState.Make
                          (TState.update TState.vcap
                             (IIS.strict (PPState.iis ppst))
                             (TState.promise p (PPState.state ppst)))
                          mem_new (PPState.iis ppst))
                (a := PPState.state
                        (PPState.Make
                           (TState.update TState.vcap
                              (IIS.strict (PPState.iis ppst))
                              (TState.promise p (PPState.state ppst)))
                           mem_new (PPState.iis ppst))).
              -- apply (Exec.elem_of_mget (E:=string)
                   (PPState.Make
                      (TState.update TState.vcap
                         (IIS.strict (PPState.iis ppst))
                         (TState.promise p (PPState.state ppst)))
                      mem_new (PPState.iis ppst)) PPState.state).
              -- cbn.
                 rewrite (TState_set_reg_promise_update_vcap p
                   (IIS.strict (PPState.iis ppst)) reg (val, 0%nat)
                   (PPState.state ppst) nts Hsetreg_eq).
                 eapply Exec.elem_of_bind_intro with
                   (st' := PPState.Make
                             (TState.update TState.vcap
                                (IIS.strict (PPState.iis ppst))
                                (TState.promise p (PPState.state ppst)))
                             mem_new (PPState.iis ppst))
                   (a := TState.promise p nts).
                 ++ apply Exec.elem_of_mret.
                 ++ cbn.
                 eapply Exec.elem_of_bind_intro with
	                   (st' := PPState.Make (TState.promise p nts)
	                             mem_new (PPState.iis ppst))
	                   (a := ()).
	                 ** change
                        (PPState.Make (TState.promise p nts) mem_new
                           (PPState.iis ppst))
                        with
                        (set PPState.state
                           (λ _ : TState.t, TState.promise p nts)
                           (PPState.Make
                              (TState.update TState.vcap
                                 (IIS.strict (PPState.iis ppst))
                                 (TState.promise p (PPState.state ppst)))
                              mem_new (PPState.iis ppst))).
                      apply Exec.elem_of_mset.
	                 ** cbn.
	                    apply Exec.elem_of_mret.
      }
      simp run_outcome in Hfull.
      rewrite Hpc in Hfull.
      unfold elem_of, Exec.elem_of_results.
      unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
      cbn in Hfull |- *.
      set_unfold.
      eapply elem_of_list_fmap_1_alt.
      * exact Hfull.
      * reflexivity.
    + unfold elem_of, Exec.elem_of_results in Hsetreg.
      rewrite Hsetreg_eq in Hsetreg.
      cbn in Hsetreg.
      exfalso.
      apply (not_elem_of_nil (pp_nts, nts)).
      exact Hsetreg.
  - apply Exec.elem_of_mret_inv in Hvreg' as [-> Hvreg'].
    inversion Hvreg'; subst vreg'.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_ts [ts [Hget Hrun]]].
    apply Exec.elem_of_mget_inv in Hget as [-> ->].
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_nts [nts [Hsetreg Hrun]]].
    unfold othrow in Hsetreg.
    destruct
      (TState.set_reg reg (val, IIS.strict (PPState.iis ppst))
         (PPState.state ppst)) as [nts0|] eqn:Hsetreg_eq.
    + rewrite Hsetreg_eq in Hsetreg.
      cbn in Hsetreg.
      apply Exec.elem_of_mret_inv in Hsetreg as [-> Hsetreg].
      inversion Hsetreg; subst nts0.
      apply Exec.elem_of_bind_elim in Hrun as
        [pp_set [[] [Hset Hrun]]].
      unfold msetv in Hset.
      apply Exec.elem_of_mSet_inv in Hset as ->.
      apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
      inversion Heq; subst ppst'.
      inversion Hret; subst eret0 vpre_opt.
      destruct (Exec.elem_of_guard_or
        (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
        (P:=racc = None)
        (PPState.Make (TState.promise p (PPState.state ppst))
           mem_new (PPState.iis ppst))
        "Non trivial reg access types unsupported" Hracc) as
        [p_racc' Hguard'].
      assert
        (Hfull :
           Exec.elem_of_results
             (PPState.Make (TState.promise p nts)
                mem_new (PPState.iis ppst), ((), None))
             (run_outcome tid initmem (RegWrite reg racc val)
                (PPState.Make (TState.promise p (PPState.state ppst))
                   mem_new (PPState.iis ppst)))).
      {
        simp run_outcome.
        eapply Exec.elem_of_bind_intro with
          (st' := PPState.Make (TState.promise p (PPState.state ppst))
                    mem_new (PPState.iis ppst))
          (a := p_racc').
        - exact Hguard'.
        - cbn.
          eapply Exec.elem_of_bind_intro with
            (st' := PPState.Make (TState.promise p (PPState.state ppst))
                      mem_new (PPState.iis ppst))
            (a := IIS.strict (PPState.iis ppst)).
          + apply (Exec.elem_of_mget (E:=string)
              (PPState.Make (TState.promise p (PPState.state ppst))
                 mem_new (PPState.iis ppst)) (IIS.strict ∘ PPState.iis)).
          + cbn.
            rewrite Hpc.
            eapply Exec.elem_of_bind_intro with
              (st' := PPState.Make (TState.promise p (PPState.state ppst))
                        mem_new (PPState.iis ppst))
              (a := IIS.strict (PPState.iis ppst)).
	            * apply Exec.elem_of_mret.
	            * cbn.
	              eapply Exec.elem_of_bind_intro with
	                (st' := PPState.Make (TState.promise p (PPState.state ppst))
	                          mem_new (PPState.iis ppst))
	                (a := PPState.state
                          (PPState.Make
                             (TState.promise p (PPState.state ppst))
                             mem_new (PPState.iis ppst))).
	              -- apply (Exec.elem_of_mget (E:=string)
                     (PPState.Make (TState.promise p (PPState.state ppst))
                        mem_new (PPState.iis ppst)) PPState.state).
	              -- cbn.
                   rewrite (TState_set_reg_promise p reg
                     (val, IIS.strict (PPState.iis ppst))
                     (PPState.state ppst) nts Hsetreg_eq).
                   eapply Exec.elem_of_bind_intro with
                     (st' := PPState.Make
                               (TState.promise p (PPState.state ppst))
                               mem_new (PPState.iis ppst))
                     (a := TState.promise p nts).
                   ++ apply Exec.elem_of_mret.
                   ++ cbn.
	                 eapply Exec.elem_of_bind_intro with
		                   (st' := PPState.Make (TState.promise p nts)
		                             mem_new (PPState.iis ppst))
		                   (a := ()).
	                 ** change
                        (PPState.Make (TState.promise p nts) mem_new
                           (PPState.iis ppst))
                        with
                        (set PPState.state
                           (λ _ : TState.t, TState.promise p nts)
                           (PPState.Make
                              (TState.promise p (PPState.state ppst))
                              mem_new (PPState.iis ppst))).
                      apply Exec.elem_of_mset.
	                 ** cbn.
	                    apply Exec.elem_of_mret.
      }
      simp run_outcome in Hfull.
      rewrite Hpc in Hfull.
      unfold elem_of, Exec.elem_of_results.
      unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
      cbn in Hfull |- *.
      set_unfold.
      eapply elem_of_list_fmap_1_alt.
      * exact Hfull.
      * reflexivity.
    + unfold elem_of, Exec.elem_of_results in Hsetreg.
      rewrite Hsetreg_eq in Hsetreg.
      cbn in Hsetreg.
      exfalso.
      apply (not_elem_of_nil (pp_nts, nts)).
      exact Hsetreg.
Qed.

Lemma reg_write_outcome_future_promise_stable_promised tid initmem msg
    reg racc val :
  outcome_future_promise_stable_promised tid initmem msg
    (RegWrite reg racc val).
Proof.
  intros ppst ppst' eret Hrun.
  assert (Hmem : PPState.mem ppst' = PPState.mem ppst).
  {
    apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
    simp run_outcome in Hraw.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_guard [p_racc [Hguard Hraw]]].
    apply Exec.elem_of_guard_or_inv in Hguard as ->.
    cbn in Hraw.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_vreg [vreg [Hvreg Hraw]]].
    apply Exec.elem_of_mget_inv in Hvreg as [-> ->].
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_vreg' [vreg' [Hvreg' Hraw]]].
    destruct (reg =? pc_reg) eqn:Hpc.
    - apply Exec.elem_of_bind_elim in Hvreg' as
        [pp_vcap [[] [Hvcap Hvreg']]].
      apply Exec.elem_of_mset_inv in Hvcap as ->.
      apply Exec.elem_of_mret_inv in Hvreg' as [-> Hvreg'].
      inversion Hvreg'; subst vreg'.
      apply Exec.elem_of_bind_elim in Hraw as
        [pp_ts [ts [Hget Hraw]]].
      apply Exec.elem_of_mget_inv in Hget as [-> ->].
      apply Exec.elem_of_bind_elim in Hraw as
        [pp_nts [nts [Hsetreg Hraw]]].
      unfold othrow in Hsetreg.
      cbn in Hsetreg.
      change
        (PPState.state
           (set PPState.state
              (TState.update TState.vcap (IIS.strict (PPState.iis ppst)))
              ppst))
        with
        (TState.update TState.vcap (IIS.strict (PPState.iis ppst))
           (PPState.state ppst)) in Hsetreg.
      destruct
        (TState.set_reg reg (val, 0%nat)
           (TState.update TState.vcap (IIS.strict (PPState.iis ppst))
              (PPState.state ppst))) as [nts0|] eqn:Hsetreg_eq.
      + rewrite Hsetreg_eq in Hsetreg.
        cbn in Hsetreg.
        apply Exec.elem_of_mret_inv in Hsetreg as [-> Hsetreg].
        inversion Hsetreg; subst nts0.
        apply Exec.elem_of_bind_elim in Hraw as
          [pp_set [[] [Hset Hraw]]].
        unfold msetv in Hset.
        apply Exec.elem_of_mSet_inv in Hset as ->.
        apply Exec.elem_of_mret_inv in Hraw as [Heq Hret].
        inversion Heq; subst ppst'; reflexivity.
      + unfold elem_of, Exec.elem_of_results in Hsetreg.
        rewrite Hsetreg_eq in Hsetreg.
        cbn in Hsetreg.
        exfalso; apply (not_elem_of_nil (pp_nts, nts)); exact Hsetreg.
    -
      apply Exec.elem_of_mret_inv in Hvreg' as [-> Hvreg'].
      inversion Hvreg'; subst vreg'.
      apply Exec.elem_of_bind_elim in Hraw as
        [pp_ts [ts [Hget Hraw]]].
      apply Exec.elem_of_mget_inv in Hget as [-> ->].
      apply Exec.elem_of_bind_elim in Hraw as
        [pp_nts [nts [Hsetreg Hraw]]].
      unfold othrow in Hsetreg.
      destruct
        (TState.set_reg reg (val, IIS.strict (PPState.iis ppst))
           (PPState.state ppst)) as [nts0|] eqn:Hsetreg_eq.
      + rewrite Hsetreg_eq in Hsetreg.
        cbn in Hsetreg.
        apply Exec.elem_of_mret_inv in Hsetreg as [-> Hsetreg].
        inversion Hsetreg; subst nts0.
        apply Exec.elem_of_bind_elim in Hraw as
          [pp_set [[] [Hset Hraw]]].
        unfold msetv in Hset.
        apply Exec.elem_of_mSet_inv in Hset as ->.
        apply Exec.elem_of_mret_inv in Hraw as [Heq Hret].
        inversion Heq; subst ppst'; reflexivity.
      + unfold elem_of, Exec.elem_of_results in Hsetreg.
        rewrite Hsetreg_eq in Hsetreg.
        cbn in Hsetreg.
        exfalso; apply (not_elem_of_nil (pp_nts, nts)); exact Hsetreg.
  }
  unfold CPState.promise_ppstate, UMPromising.
  cbn.
  rewrite Hmem.
  eapply reg_write_outcome_promise_state_fmap.
  exact Hrun.
Qed.

Lemma mem_write_addr_announce_outcome_promise_state_fmap tid initmem req
    ppst ppst' p mem_new eret :
  Exec.elem_of_results (ppst', eret)
    ((run_outcome tid initmem (MemWriteAddrAnnounce req) |$> fst) ppst) →
  Exec.elem_of_results
    (PPState.Make (TState.promise p (PPState.state ppst'))
       mem_new (PPState.iis ppst'), eret)
    ((run_outcome tid initmem (MemWriteAddrAnnounce req) |$> fst)
       (PPState.Make (TState.promise p (PPState.state ppst))
          mem_new (PPState.iis ppst))).
Proof.
  intro Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hrun]].
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_vaddr [vaddr [Hvaddr Hrun]]].
  apply Exec.elem_of_mget_inv in Hvaddr as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_state [[] [Hstate Hrun]]].
  apply Exec.elem_of_mset_inv in Hstate as ->.
  apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
  inversion Heq; subst ppst'.
  inversion Hret; subst eret0 vpre_opt.
  assert
    (Hfull :
       Exec.elem_of_results
         (PPState.Make
            (TState.promise p
               (TState.update TState.vcap (IIS.strict (PPState.iis ppst))
                  (PPState.state ppst)))
            mem_new (PPState.iis ppst), ((), None))
         (run_outcome tid initmem (MemWriteAddrAnnounce req)
            (PPState.Make (TState.promise p (PPState.state ppst))
               mem_new (PPState.iis ppst)))).
  {
    simp run_outcome.
    eapply Exec.elem_of_bind_intro with
      (e := (mget (IIS.strict ∘ PPState.iis) :
               Exec.t (PPState.t TState.t Msg.t IIS.t) string nat))
      (st' := PPState.Make (TState.promise p (PPState.state ppst))
                mem_new (PPState.iis ppst))
      (a := IIS.strict (PPState.iis ppst)).
    - apply (Exec.elem_of_mget (E:=string)
        (PPState.Make (TState.promise p (PPState.state ppst))
           mem_new (PPState.iis ppst)) (IIS.strict ∘ PPState.iis)).
    - cbn.
      eapply Exec.elem_of_bind_intro with
        (st' := PPState.Make
                  (TState.promise p
                     (TState.update TState.vcap
                        (IIS.strict (PPState.iis ppst))
                        (PPState.state ppst)))
                  mem_new (PPState.iis ppst))
        (a := ()).
      + change
          (PPState.Make
             (TState.promise p
                (TState.update TState.vcap
                   (IIS.strict (PPState.iis ppst))
                   (PPState.state ppst)))
             mem_new (PPState.iis ppst))
          with
          (PPState.Make
             (TState.update TState.vcap
                (IIS.strict (PPState.iis ppst))
                (TState.promise p (PPState.state ppst)))
             mem_new (PPState.iis ppst)).
        change
          (PPState.Make
             (TState.update TState.vcap
                (IIS.strict (PPState.iis ppst))
                (TState.promise p (PPState.state ppst)))
             mem_new (PPState.iis ppst))
          with
          (set PPState.state
             (TState.update TState.vcap (IIS.strict (PPState.iis ppst)))
             (PPState.Make (TState.promise p (PPState.state ppst))
                mem_new (PPState.iis ppst))).
        apply Exec.elem_of_mset.
      + cbn.
        apply Exec.elem_of_mret.
  }
  unfold elem_of, Exec.elem_of_results.
  unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  set_unfold.
  cbn.
  rewrite TState_promise_update_vcap.
  apply elem_of_list_singleton.
  reflexivity.
Qed.

Lemma mem_write_addr_announce_outcome_future_promise_stable_promised
    tid initmem msg req :
  outcome_future_promise_stable_promised tid initmem msg
    (MemWriteAddrAnnounce req).
Proof.
  intros ppst ppst' eret Hrun.
  assert (Hmem : PPState.mem ppst' = PPState.mem ppst).
  {
    apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
    simp run_outcome in Hraw.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_vaddr [vaddr [Hvaddr Hraw]]].
    apply Exec.elem_of_mget_inv in Hvaddr as [-> ->].
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_state [[] [Hstate Hraw]]].
    apply Exec.elem_of_mset_inv in Hstate as ->.
    apply Exec.elem_of_mret_inv in Hraw as [Heq Hret].
    inversion Heq; subst ppst'.
    reflexivity.
  }
  unfold CPState.promise_ppstate, UMPromising.
  cbn.
  rewrite Hmem.
  eapply mem_write_addr_announce_outcome_promise_state_fmap.
  exact Hrun.
Qed.

Lemma barrier_dmb_outcome_future_promise_stable_promised tid initmem msg
    dmb :
  outcome_future_promise_stable_promised tid initmem msg
    (Barrier (Barrier_DMB dmb)).
Proof.
  intros ppst ppst' eret Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
  simp run_outcome in Hraw.
  apply Exec.elem_of_bind_elim in Hraw as [pp_ts [ts [Hget Hraw]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  destruct dmb.(DxB_types) eqn:Hdmb.
  all: apply Exec.elem_of_bind_elim in Hraw as
    [pp_state [[] [Hstate Hraw]]].
  all: apply Exec.elem_of_mset_inv in Hstate as ->.
  all: apply Exec.elem_of_mret_inv in Hraw as [Heq Hret].
  all: inversion Heq; subst ppst'.
  all: inversion Hret; subst eret0 vpre_opt.
  all: unfold CPState.promise_ppstate, UMPromising; cbn.
  all: unfold elem_of, Exec.elem_of_results.
  all: unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  all: set_unfold; cbn; simp run_outcome; cbn; rewrite Hdmb; cbn.
  - eapply elem_of_list_fmap_1_alt with
      (x := (PPState.Make
               (TState.update TState.vdmb
                  (TState.vrd (PPState.state ppst))
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst)))
               (msg :: PPState.mem ppst) (PPState.iis ppst),
             ((), None))).
    + eapply Exec.elem_of_bind_intro with
        (st' := PPState.Make
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst))
                  (msg :: PPState.mem ppst) (PPState.iis ppst))
        (a := TState.promise (S (length (PPState.mem ppst)))
                (PPState.state ppst)).
      * apply (Exec.elem_of_mget (E:=string)
          (PPState.Make
             (TState.promise (S (length (PPState.mem ppst)))
                (PPState.state ppst))
             (msg :: PPState.mem ppst) (PPState.iis ppst)) PPState.state).
      * cbn.
        eapply Exec.elem_of_bind_intro with
          (st' := PPState.Make
                    (TState.update TState.vdmb
                       (TState.vrd (PPState.state ppst))
                       (TState.promise (S (length (PPState.mem ppst)))
                          (PPState.state ppst)))
                    (msg :: PPState.mem ppst) (PPState.iis ppst))
          (a := ()).
        -- change
             (PPState.Make
                (TState.update TState.vdmb
                   (TState.vrd (PPState.state ppst))
                   (TState.promise (S (length (PPState.mem ppst)))
                      (PPState.state ppst)))
                (msg :: PPState.mem ppst) (PPState.iis ppst))
             with
             (set PPState.state
                (TState.update TState.vdmb
                   (TState.vrd (PPState.state ppst)))
                (PPState.Make
                   (TState.promise (S (length (PPState.mem ppst)))
                      (PPState.state ppst))
                   (msg :: PPState.mem ppst) (PPState.iis ppst))).
           apply Exec.elem_of_mset.
        -- cbn.
           apply Exec.elem_of_mret.
    + cbn.
      rewrite TState_promise_update_vdmb.
      reflexivity.
  - eapply elem_of_list_fmap_1_alt with
      (x := (PPState.Make
               (TState.update TState.vdmbst
                  (TState.vwr (PPState.state ppst))
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst)))
               (msg :: PPState.mem ppst) (PPState.iis ppst),
             ((), None))).
    + eapply Exec.elem_of_bind_intro with
        (st' := PPState.Make
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst))
                  (msg :: PPState.mem ppst) (PPState.iis ppst))
        (a := TState.promise (S (length (PPState.mem ppst)))
                (PPState.state ppst)).
      * apply (Exec.elem_of_mget (E:=string)
          (PPState.Make
             (TState.promise (S (length (PPState.mem ppst)))
                (PPState.state ppst))
             (msg :: PPState.mem ppst) (PPState.iis ppst)) PPState.state).
      * cbn.
        eapply Exec.elem_of_bind_intro with
          (st' := PPState.Make
                    (TState.update TState.vdmbst
                       (TState.vwr (PPState.state ppst))
                       (TState.promise (S (length (PPState.mem ppst)))
                          (PPState.state ppst)))
                    (msg :: PPState.mem ppst) (PPState.iis ppst))
          (a := ()).
        -- change
             (PPState.Make
                (TState.update TState.vdmbst
                   (TState.vwr (PPState.state ppst))
                   (TState.promise (S (length (PPState.mem ppst)))
                      (PPState.state ppst)))
                (msg :: PPState.mem ppst) (PPState.iis ppst))
             with
             (set PPState.state
                (TState.update TState.vdmbst
                   (TState.vwr (PPState.state ppst)))
                (PPState.Make
                   (TState.promise (S (length (PPState.mem ppst)))
                      (PPState.state ppst))
                   (msg :: PPState.mem ppst) (PPState.iis ppst))).
           apply Exec.elem_of_mset.
        -- cbn.
           apply Exec.elem_of_mret.
    + cbn.
      rewrite TState_promise_update_vdmbst.
      reflexivity.
  - eapply elem_of_list_fmap_1_alt with
      (x := (PPState.Make
               (TState.update TState.vdmb
                  (TState.vrd (PPState.state ppst) ⊔
                   TState.vwr (PPState.state ppst))
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst)))
               (msg :: PPState.mem ppst) (PPState.iis ppst),
             ((), None))).
    + eapply Exec.elem_of_bind_intro with
        (st' := PPState.Make
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst))
                  (msg :: PPState.mem ppst) (PPState.iis ppst))
        (a := TState.promise (S (length (PPState.mem ppst)))
                (PPState.state ppst)).
      * apply (Exec.elem_of_mget (E:=string)
          (PPState.Make
             (TState.promise (S (length (PPState.mem ppst)))
                (PPState.state ppst))
             (msg :: PPState.mem ppst) (PPState.iis ppst)) PPState.state).
      * cbn.
        eapply Exec.elem_of_bind_intro with
          (st' := PPState.Make
                    (TState.update TState.vdmb
                       (TState.vrd (PPState.state ppst) ⊔
                        TState.vwr (PPState.state ppst))
                       (TState.promise (S (length (PPState.mem ppst)))
                          (PPState.state ppst)))
                    (msg :: PPState.mem ppst) (PPState.iis ppst))
          (a := ()).
        -- change
             (PPState.Make
                (TState.update TState.vdmb
                   (TState.vrd (PPState.state ppst) ⊔
                    TState.vwr (PPState.state ppst))
                   (TState.promise (S (length (PPState.mem ppst)))
                      (PPState.state ppst)))
                (msg :: PPState.mem ppst) (PPState.iis ppst))
             with
             (set PPState.state
                (TState.update TState.vdmb
                   (TState.vrd (PPState.state ppst) ⊔
                    TState.vwr (PPState.state ppst)))
                (PPState.Make
                   (TState.promise (S (length (PPState.mem ppst)))
                      (PPState.state ppst))
                   (msg :: PPState.mem ppst) (PPState.iis ppst))).
           apply Exec.elem_of_mset.
        -- cbn.
           apply Exec.elem_of_mret.
    + cbn.
      rewrite TState_promise_update_vdmb.
      reflexivity.
Qed.

Lemma barrier_isb_outcome_future_promise_stable_promised tid initmem msg :
  outcome_future_promise_stable_promised tid initmem msg
    (Barrier (Barrier_ISB ())).
Proof.
  intros ppst ppst' eret Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
  simp run_outcome in Hraw.
  apply Exec.elem_of_bind_elim in Hraw as [pp_ts [ts [Hget Hraw]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_state [[] [Hstate Hraw]]].
  apply Exec.elem_of_mset_inv in Hstate as ->.
  apply Exec.elem_of_mret_inv in Hraw as [Heq Hret].
  inversion Heq; subst ppst'.
  inversion Hret; subst eret0 vpre_opt.
  unfold CPState.promise_ppstate, UMPromising.
  cbn.
  unfold elem_of, Exec.elem_of_results.
  unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  set_unfold.
  cbn.
  simp run_outcome.
  cbn.
  eapply elem_of_list_fmap_1_alt with
    (x := (PPState.Make
             (TState.update TState.visb (TState.vcap (PPState.state ppst))
                (TState.promise (S (length (PPState.mem ppst)))
                   (PPState.state ppst)))
             (msg :: PPState.mem ppst) (PPState.iis ppst),
           ((), None))).
  - eapply Exec.elem_of_bind_intro with
      (st' := PPState.Make
                (TState.promise (S (length (PPState.mem ppst)))
                   (PPState.state ppst))
                (msg :: PPState.mem ppst) (PPState.iis ppst))
      (a := TState.promise (S (length (PPState.mem ppst)))
              (PPState.state ppst)).
    + apply (Exec.elem_of_mget (E:=string)
        (PPState.Make
           (TState.promise (S (length (PPState.mem ppst)))
              (PPState.state ppst))
           (msg :: PPState.mem ppst) (PPState.iis ppst)) PPState.state).
    + cbn.
      eapply Exec.elem_of_bind_intro with
        (st' := PPState.Make
                  (TState.update TState.visb
                     (TState.vcap (PPState.state ppst))
                     (TState.promise (S (length (PPState.mem ppst)))
                        (PPState.state ppst)))
                  (msg :: PPState.mem ppst) (PPState.iis ppst))
        (a := ()).
      * change
          (PPState.Make
             (TState.update TState.visb
                (TState.vcap (PPState.state ppst))
                (TState.promise (S (length (PPState.mem ppst)))
                   (PPState.state ppst)))
             (msg :: PPState.mem ppst) (PPState.iis ppst))
          with
          (set PPState.state
             (TState.update TState.visb (TState.vcap (PPState.state ppst)))
             (PPState.Make
                (TState.promise (S (length (PPState.mem ppst)))
                   (PPState.state ppst))
                (msg :: PPState.mem ppst) (PPState.iis ppst))).
        apply Exec.elem_of_mset.
      * cbn.
        apply Exec.elem_of_mret.
  - cbn.
    rewrite TState_promise_update_visb.
    reflexivity.
Qed.

Lemma UMPromising_imon_future_promise_stable_to_cmon {n}
    (tid : fin n) initmem code msg A (mon : iMon A) :
  imon_future_promise_stable_fmap (tid : nat) initmem code msg A mon →
  CPState.cmon_handle_outcome_cons_event_stable UMPromising
    tid initmem msg A mon.
Proof.
  revert mon.
  induction mon as [a|call k IH]; intro Hstable.
  - cbn.
    exact I.
  - cbn in Hstable |- *.
    destruct call as [out|choice].
    + destruct Hstable as [Hout Hk].
      split.
      * exact Hout.
      * intro eret.
        apply IH.
        apply Hk.
    + intro ret.
      apply IH.
      apply Hstable.
Qed.

Lemma UMPromising_run_tid_cons_event_stable_from_imon {n}
    (isem : iMon ()) (term : terminationCondition n) (tid : fin n)
    initmem code msg st st' :
  initmem = CPState.initmem st →
  imon_future_promise_stable_fmap (tid : nat) initmem code msg () isem →
  Exec.elem_of_results (st', ()) (CPState.run_tid isem UMPromising tid st) →
  Exec.elem_of_results
    (CPState.cons_event_state UMPromising msg st', ())
    (CPState.run_tid isem UMPromising tid
       (CPState.cons_event_state UMPromising msg st)).
Proof.
  intros Hinit Hstable Hrun.
  eapply CPState.run_tid_cons_event_stable_mon.
  - exact Hinit.
  - apply (UMPromising_imon_future_promise_stable_to_cmon
      tid initmem code msg () isem).
    exact Hstable.
  - exact Hrun.
Qed.

Lemma UMPromising_run_to_termination_plain_cons_event_stable_from_imon {n}
    (isem : iMon ()) (term : terminationCondition n) (tid : fin n)
    initmem code msg fuel ppst ppst' b :
  imon_future_promise_stable_fmap (tid : nat) initmem code msg () isem →
  Exec.elem_of_results (ppst', b)
    (CPState.run_to_termination_plain isem UMPromising term
       tid initmem fuel ppst) →
  Exec.elem_of_results
    (CPState.cons_event_ppstate UMPromising msg ppst', b)
    (CPState.run_to_termination_plain isem UMPromising term
       tid initmem fuel
       (CPState.cons_event_ppstate UMPromising msg ppst)).
Proof.
  intros Hstable Hrun.
  eapply CPState.run_to_termination_plain_cons_event_stable_mon.
  - apply (UMPromising_imon_future_promise_stable_to_cmon
      tid initmem code msg () isem).
    exact Hstable.
  - exact Hrun.
Qed.

Lemma UMPromising_imon_future_promise_stable_promised_to_cmon {n}
    (tid : fin n) initmem msg A (mon : iMon A) :
  imon_future_promise_stable_promised (tid : nat) initmem msg A mon →
  CPState.cmon_handle_outcome_promise_ppstate_stable UMPromising
    tid initmem msg A mon.
Proof.
  revert mon.
  induction mon as [a|call k IH]; intro Hstable.
  - cbn.
    exact I.
  - cbn in Hstable |- *.
    destruct call as [out|choice].
    + destruct Hstable as [Hout Hk].
      split.
      * exact Hout.
      * intro eret.
        apply IH.
        apply Hk.
    + intro ret.
      apply IH.
      apply Hstable.
Qed.

Lemma UMPromising_run_tid_promise_same_stable_from_imon {n}
    (isem : iMon ()) (term : terminationCondition n) (tid : fin n)
    initmem msg st st' :
  initmem = CPState.initmem st →
  imon_future_promise_stable_promised
    (tid : nat) initmem msg () isem →
  Exec.elem_of_results (st', ()) (CPState.run_tid isem UMPromising tid st) →
  Exec.elem_of_results
    (CPState.promise_tid UMPromising tid msg st', ())
    (CPState.run_tid isem UMPromising tid
       (CPState.promise_tid UMPromising tid msg st)).
Proof.
  intros Hinit Hstable Hrun.
  eapply CPState.run_tid_promise_same_stable_mon.
  - exact Hinit.
  - apply (UMPromising_imon_future_promise_stable_promised_to_cmon
      tid initmem msg () isem).
    exact Hstable.
  - exact Hrun.
Qed.

Lemma UMPromising_run_to_termination_plain_promise_same_stable_from_imon {n}
    (isem : iMon ()) (term : terminationCondition n) (tid : fin n)
    initmem msg fuel ppst ppst' b :
  imon_future_promise_stable_promised
    (tid : nat) initmem msg () isem →
  Exec.elem_of_results (ppst', b)
    (CPState.run_to_termination_plain isem UMPromising term
       tid initmem fuel ppst) →
  Exec.elem_of_results
    (CPState.promise_ppstate UMPromising tid initmem msg ppst', b)
    (CPState.run_to_termination_plain isem UMPromising term
       tid initmem fuel
       (CPState.promise_ppstate UMPromising tid initmem msg ppst)).
Proof.
  intros Hstable Hrun.
  eapply CPState.run_to_termination_plain_promise_ppstate_stable_mon.
  - intro ppst0.
    destruct ppst0 as [ts mem iis0].
    cbn.
    rewrite TState_reg_map_promise.
    reflexivity.
  - apply (UMPromising_imon_future_promise_stable_promised_to_cmon
      tid initmem msg () isem).
    exact Hstable.
  - exact Hrun.
Qed.

Record UMPromising_tail_stable {n} (isem : iMon ()) : Prop := {
    UMPromising_tail_same_promise_stable :
      ∀ (tid : fin n) (initmem : memoryMap) (msg : Msg.t),
        imon_future_promise_stable_promised
          (tid : nat) initmem msg () isem;
    UMPromising_tail_future_event_stable :
      ∀ (tid : fin n) (initmem : memoryMap) (code : code_region)
          (msg : Msg.t),
        imon_future_promise_stable_fmap
          (tid : nat) initmem code msg () isem;
  }.

Fixpoint UMPromising_Sail_promised_stable tid initmem msg nondet
    {A eo} (smon : SI.iMon eo A) : Prop :=
  match smon with
  | SI.Ret _ => True
  | SI.Next out k =>
      imon_future_promise_stable_promised tid initmem msg _
        (Sail_outcome_interp nondet out) ∧
      ∀ ret,
        UMPromising_Sail_promised_stable tid initmem msg nondet (k ret)
  end.

Fixpoint UMPromising_Sail_fmap_stable tid initmem code msg nondet
    {A eo} (smon : SI.iMon eo A) : Prop :=
  match smon with
  | SI.Ret _ => True
  | SI.Next out k =>
      imon_future_promise_stable_fmap tid initmem code msg _
        (Sail_outcome_interp nondet out) ∧
      ∀ ret,
        UMPromising_Sail_fmap_stable tid initmem code msg nondet (k ret)
  end.

Lemma UMPromising_imon_promised_stable_bind tid initmem msg
    {A B} (mon : iMon A) (k : A → iMon B) :
  imon_future_promise_stable_promised tid initmem msg A mon →
  (∀ a, imon_future_promise_stable_promised tid initmem msg B (k a)) →
  imon_future_promise_stable_promised tid initmem msg B
    (a ← mon; k a).
Proof.
  revert k.
  induction mon as [a|call kmon IH]; intros k Hmon Hk; cbn in Hmon |- *.
  - apply Hk.
  - destruct call as [out|choice].
    + destruct Hmon as [Hout Hmon].
      split.
      * exact Hout.
      * intro eret.
        apply IH.
        -- apply Hmon.
        -- exact Hk.
    + intro ret.
      apply IH.
      * apply Hmon.
      * exact Hk.
Qed.

Lemma UMPromising_imon_fmap_stable_bind tid initmem code msg
    {A B} (mon : iMon A) (k : A → iMon B) :
  imon_future_promise_stable_fmap tid initmem code msg A mon →
  (∀ a, imon_future_promise_stable_fmap tid initmem code msg B (k a)) →
  imon_future_promise_stable_fmap tid initmem code msg B (a ← mon; k a).
Proof.
  revert k.
  induction mon as [a|call kmon IH]; intros k Hmon Hk; cbn in Hmon |- *.
  - apply Hk.
  - destruct call as [out|choice].
    + destruct Hmon as [Hout Hmon].
      split.
      * exact Hout.
      * intro eret.
        apply IH.
        -- apply Hmon.
        -- exact Hk.
    + intro ret.
      apply IH.
      * apply Hmon.
      * exact Hk.
Qed.

Lemma UMPromising_iMon_from_Sail_promised_stable tid initmem msg nondet
    {A eo} (smon : SI.iMon eo A) :
  UMPromising_Sail_promised_stable tid initmem msg nondet smon →
  imon_future_promise_stable_promised tid initmem msg A
    (iMon_from_Sail nondet smon).
Proof.
  induction smon as [a|out k IH]; cbn.
  - intro Hstable.
    exact I.
  - rename H into Hind.
    intros [Hout Hk].
    eapply UMPromising_imon_promised_stable_bind.
    + exact Hout.
    + intro eret.
      apply Hind.
      apply Hk.
Qed.

Lemma UMPromising_iMon_from_Sail_fmap_stable tid initmem code msg nondet
    {A eo} (smon : SI.iMon eo A) :
  UMPromising_Sail_fmap_stable tid initmem code msg nondet smon →
  imon_future_promise_stable_fmap tid initmem code msg A
    (iMon_from_Sail nondet smon).
Proof.
  induction smon as [a|out k IH]; cbn.
  - intro Hstable.
    exact I.
  - rename H into Hind.
    intros [Hout Hk].
    eapply UMPromising_imon_fmap_stable_bind.
    + exact Hout.
    + intro eret.
      apply Hind.
      apply Hk.
Qed.

Record UMPromising_Sail_tail_stable {n eo} nondet
    (smon : SI.iMon eo ()) : Prop := {
    UMPromising_Sail_tail_same_promise_stable :
      ∀ (tid : fin n) (initmem : memoryMap) (msg : Msg.t),
        UMPromising_Sail_promised_stable
          (tid : nat) initmem msg nondet smon;
    UMPromising_Sail_tail_future_event_stable :
      ∀ (tid : fin n) (initmem : memoryMap) (code : code_region)
          (msg : Msg.t),
        UMPromising_Sail_fmap_stable
          (tid : nat) initmem code msg nondet smon;
  }.

Record UMPromising_Sail_same_promise_stable {n eo} nondet
    (smon : SI.iMon eo ()) : Prop := {
    UMPromising_Sail_same_promised_stable :
      ∀ (tid : fin n) (initmem : memoryMap) (msg : Msg.t),
        UMPromising_Sail_promised_stable
          (tid : nat) initmem msg nondet smon;
  }.

Record UMPromising_read_code_stability (tid : nat)
    (initmem : memoryMap) (code : code_region) (msg : Msg.t) : Prop := {
    UMPromising_read_code_ifetch_stable :
      ∀ (addr : address) (size : N) (macc : mem_acc)
          (addr_space : addr_space),
        is_ifetch macc = true →
        event_misses_code code msg ∧ ifetch_in_code code addr size;
    UMPromising_read_code_explicit_read_bound :
      ∀ (ppst : PPState.t TState.t Msg.t IIS.t)
          (addr : address) (size : N) (macc : mem_acc)
          (addr_space : addr_space),
        is_ifetch macc = false →
        is_explicit macc = true →
        ppstate_read_times_le macc ppst;
  }.

Lemma UMPromising_mem_read_promised_stable_from_read_code
    tid initmem code msg addr size macc addr_space :
  UMPromising_read_code_stability tid initmem code msg →
  outcome_future_promise_stable_promised tid initmem msg
    (MemRead (MemReq.make macc addr addr_space size 0)).
Proof.
  intro Hstable.
  destruct Hstable as [Hifetch Hbound].
  apply mem_read_outcome_future_promise_stable_promised with
    (code := code).
  - apply (Hifetch addr size macc addr_space).
  - intros ppst Hnot_ifetch Hexplicit.
    eapply Hbound; eauto.
Qed.

Lemma UMPromising_mem_read_fmap_stable_from_read_code
    tid initmem code msg addr size macc addr_space :
  UMPromising_read_code_stability tid initmem code msg →
  outcome_future_promise_stable_fmap tid initmem code msg
    (MemRead (MemReq.make macc addr addr_space size 0)).
Proof.
  intro Hstable.
  destruct Hstable as [Hifetch Hbound].
  apply mem_read_outcome_future_promise_stable_fmap.
  - apply (Hifetch addr size macc addr_space).
  - intros ppst Hnot_ifetch Hexplicit.
    eapply Hbound; eauto.
Qed.

Ltac solve_UMPromising_unsupported_promised_stable :=
  intros ppst ppst' eret Hrun;
  cbn in Hrun;
  unfold mthrow, Exec.throw_inst, Exec.res_throw_inst in Hrun;
  unfold elem_of, Exec.elem_of_results in Hrun;
  cbn in Hrun;
  inversion Hrun.

Lemma UMPromising_cache_op_outcome_future_promise_stable_promised
    tid initmem msg cop :
  outcome_future_promise_stable_promised tid initmem msg
    (CacheOp cop).
Proof.
  solve_UMPromising_unsupported_promised_stable.
Qed.

Lemma UMPromising_tlbop_outcome_future_promise_stable_promised
    tid initmem msg tlbi :
  outcome_future_promise_stable_promised tid initmem msg
    (TlbOp tlbi).
Proof.
  solve_UMPromising_unsupported_promised_stable.
Qed.

Lemma UMPromising_take_exception_outcome_future_promise_stable_promised
    tid initmem msg fault :
  outcome_future_promise_stable_promised tid initmem msg
    (TakeException fault).
Proof.
  solve_UMPromising_unsupported_promised_stable.
Qed.

Lemma UMPromising_return_exception_outcome_future_promise_stable_promised
    tid initmem msg :
  outcome_future_promise_stable_promised tid initmem msg ReturnException.
Proof.
  solve_UMPromising_unsupported_promised_stable.
Qed.

Lemma UMPromising_translation_start_outcome_future_promise_stable_promised
    tid initmem msg ts :
  outcome_future_promise_stable_promised tid initmem msg
    (TranslationStart ts).
Proof.
  solve_UMPromising_unsupported_promised_stable.
Qed.

Lemma UMPromising_translation_end_outcome_future_promise_stable_promised
    tid initmem msg te :
  outcome_future_promise_stable_promised tid initmem msg
    (TranslationEnd te).
Proof.
  solve_UMPromising_unsupported_promised_stable.
Qed.

Lemma UMPromising_barrier_dsb_outcome_future_promise_stable_promised
    tid initmem msg dsb :
  outcome_future_promise_stable_promised tid initmem msg
    (Barrier (Barrier_DSB dsb)).
Proof.
  solve_UMPromising_unsupported_promised_stable.
Qed.

Lemma UMPromising_generic_fail_outcome_future_promise_stable_promised
    tid initmem msg s :
  outcome_future_promise_stable_promised tid initmem msg
    (GenericFail s).
Proof.
  intros ppst ppst' [].
Qed.

Lemma UMPromising_mem_read_nonzero_tag_promised_stable tid initmem msg
    addr size macc addr_space tag :
  outcome_future_promise_stable_promised tid initmem msg
    (MemRead (MemReq.make macc addr addr_space size (N.pos tag))).
Proof.
  solve_UMPromising_unsupported_promised_stable.
Qed.

Lemma UMPromising_tail_stable_from_Sail {n eo} nondet
    (smon : SI.iMon eo ()) :
  UMPromising_Sail_tail_stable (n:=n) nondet smon →
  UMPromising_tail_stable (n:=n) (iMon_from_Sail nondet smon).
Proof.
  intro Hstable.
  constructor.
  - intros tid initmem msg.
    apply UMPromising_iMon_from_Sail_promised_stable.
    apply UMPromising_Sail_tail_same_promise_stable.
    exact Hstable.
  - intros tid initmem code msg.
    apply UMPromising_iMon_from_Sail_fmap_stable.
    apply UMPromising_Sail_tail_future_event_stable.
    exact Hstable.
Qed.

Lemma UMPromising_Sail_same_promise_stable_from_tail_stable
    {n eo} nondet (smon : SI.iMon eo ()) :
  UMPromising_Sail_tail_stable (n:=n) nondet smon →
  UMPromising_Sail_same_promise_stable (n:=n) nondet smon.
Proof.
  intro Hstable.
  constructor.
  intros tid initmem msg.
  apply UMPromising_Sail_tail_same_promise_stable.
  exact Hstable.
Qed.

Lemma UMPromising_tail_stable_run_tid_promise_same {n}
    (isem : iMon ()) (term : terminationCondition n) (tid : fin n)
    (initmem : memoryMap) (msg : Msg.t) st st' :
  UMPromising_tail_stable (n:=n) isem →
  initmem = CPState.initmem st →
  Exec.elem_of_results (st', ()) (CPState.run_tid isem UMPromising tid st) →
  Exec.elem_of_results
    (CPState.promise_tid UMPromising tid msg st', ())
    (CPState.run_tid isem UMPromising tid
       (CPState.promise_tid UMPromising tid msg st)).
Proof.
  intros Hstable Hinit Hrun.
  destruct Hstable as [Hsame _].
  eapply (UMPromising_run_tid_promise_same_stable_from_imon
    isem term tid initmem msg st st').
  - exact Hinit.
  - exact (Hsame tid initmem msg).
  - exact Hrun.
Qed.

Lemma UMPromising_tail_stable_run_to_termination_plain_promise_same {n}
    (isem : iMon ()) (term : terminationCondition n) (tid : fin n)
    (initmem : memoryMap) (msg : Msg.t) fuel ppst ppst' b :
  UMPromising_tail_stable (n:=n) isem →
  Exec.elem_of_results (ppst', b)
    (CPState.run_to_termination_plain isem UMPromising term
       tid initmem fuel ppst) →
  Exec.elem_of_results
    (CPState.promise_ppstate UMPromising tid initmem msg ppst', b)
    (CPState.run_to_termination_plain isem UMPromising term
       tid initmem fuel
       (CPState.promise_ppstate UMPromising tid initmem msg ppst)).
Proof.
  intros Hstable Hrun.
  destruct Hstable as [Hsame _].
  eapply (UMPromising_run_to_termination_plain_promise_same_stable_from_imon
    isem term tid initmem msg fuel ppst ppst' b).
  - exact (Hsame tid initmem msg).
  - exact Hrun.
Qed.

Lemma UMPromising_tail_stable_run_tid_cons_event {n}
    (isem : iMon ()) (term : terminationCondition n) (tid : fin n)
    (initmem : memoryMap) (code : code_region) (msg : Msg.t) st st' :
  UMPromising_tail_stable (n:=n) isem →
  initmem = CPState.initmem st →
  Exec.elem_of_results (st', ()) (CPState.run_tid isem UMPromising tid st) →
  Exec.elem_of_results
    (CPState.cons_event_state UMPromising msg st', ())
    (CPState.run_tid isem UMPromising tid
       (CPState.cons_event_state UMPromising msg st)).
Proof.
  intros Hstable Hinit Hrun.
  destruct Hstable as [_ Hfuture].
  eapply (UMPromising_run_tid_cons_event_stable_from_imon
    isem term tid initmem code msg st st').
  - exact Hinit.
  - exact (Hfuture tid initmem code msg).
  - exact Hrun.
Qed.

Lemma UMPromising_tail_stable_run_to_termination_plain_cons_event {n}
    (isem : iMon ()) (term : terminationCondition n) (tid : fin n)
    (initmem : memoryMap) (code : code_region) (msg : Msg.t)
    fuel ppst ppst' b :
  UMPromising_tail_stable (n:=n) isem →
  Exec.elem_of_results (ppst', b)
    (CPState.run_to_termination_plain isem UMPromising term
       tid initmem fuel ppst) →
  Exec.elem_of_results
    (CPState.cons_event_ppstate UMPromising msg ppst', b)
    (CPState.run_to_termination_plain isem UMPromising term
       tid initmem fuel
       (CPState.cons_event_ppstate UMPromising msg ppst)).
Proof.
  intros Hstable Hrun.
  destruct Hstable as [_ Hfuture].
  eapply (UMPromising_run_to_termination_plain_cons_event_stable_from_imon
    isem term tid initmem code msg fuel ppst ppst' b).
  - exact (Hfuture tid initmem code msg).
  - exact Hrun.
Qed.

Lemma UMPromising_replayable : Promising.Replayable UMPromising.
Proof.
  constructor.
  - intros tid0 initmem0 out ppst ppst' eret H.
    exact (run_outcome_none_preserves_mem
      tid0 initmem0 out ppst ppst' eret H).
  - intros tid0 initmem0 out ppst ppst' eret vpre H.
    destruct (run_outcome_promise_replay_one
      tid0 initmem0 out ppst ppst' eret vpre H) as
      [event [Hmem [Htid [Hlt Hreplay]]]].
    exists event.
    repeat split; try assumption.
    unfold Promising.promise_ppstate.
    cbn.
    rewrite Hmem in Hreplay.
    cbn in Hreplay.
    exact Hreplay.
Qed.

Lemma UMPromising_handle_outcome_no_promise_non_mem_write {n}
    (tid : fin n) initmem out :
  (∀ mr (val : bv (8 * mr.(MemReq.size)))
      (tags : bv mr.(MemReq.num_tag)),
    out ≠ MemWrite mr val tags) →
  CPState.handle_outcome_no_promise UMPromising tid initmem out.
Proof.
  intros Hnot ppst ppst' eret vpre Hrun.
  cbn in Hrun.
  eapply run_outcome_no_promise_non_mem_write; eauto.
Qed.

Definition UMPromising_Sail_outcome_no_promise {eo A}
    (out : SI.outcome eo A) : Prop :=
  match out with
  | SI.MemWrite _ _ _ => False
  | _ => True
  end.

Fixpoint UMPromising_Sail_no_promise {eo A}
    (smon : SI.iMon eo A) : Prop :=
  match smon with
  | SI.Ret _ => True
  | SI.Next out k =>
      UMPromising_Sail_outcome_no_promise out ∧
      ∀ ret, UMPromising_Sail_no_promise (k ret)
  end.

Fixpoint UMPromising_Sail_at_most_one_promise {eo A}
    (smon : SI.iMon eo A) : Prop :=
  match smon with
  | SI.Ret _ => True
  | SI.Next out k =>
      (UMPromising_Sail_outcome_no_promise out ∧
       ∀ ret, UMPromising_Sail_at_most_one_promise (k ret)) ∨
      (∀ ret, UMPromising_Sail_no_promise (k ret))
  end.

Definition UMPromising_Sail_outcome_promised_stable tid initmem msg
    nondet {eo A} (out : SI.outcome eo A) : Prop :=
  imon_future_promise_stable_promised tid initmem msg _
    (Sail_outcome_interp nondet out).

Fixpoint UMPromising_Sail_prefix_promised_stable tid initmem msg
    nondet {eo A} (smon : SI.iMon eo A) : Prop :=
  match smon with
  | SI.Ret _ => True
  | SI.Next out k =>
      (UMPromising_Sail_outcome_no_promise out ∧
       UMPromising_Sail_outcome_promised_stable
         tid initmem msg nondet out ∧
       ∀ ret,
         UMPromising_Sail_prefix_promised_stable
           tid initmem msg nondet (k ret)) ∨
      (∀ ret, UMPromising_Sail_no_promise (k ret))
  end.

Lemma UMPromising_Sail_outcome_promised_stable_from_read_code
    tid initmem code msg nondet {eo A} (out : SI.outcome eo A) :
  UMPromising_read_code_stability tid initmem code msg →
  UMPromising_Sail_outcome_no_promise out →
  UMPromising_Sail_outcome_promised_stable
    tid initmem msg nondet out.
Proof.
  intros Hstable Hno.
  destruct out as
    [reg acc | reg acc val | rr | wr val tags | aa | opcode
    | sz pa | bar | cop | tlbi | fault | | ts | te | extra | s
    | | | ct | | message];
    cbn in Hno;
    cbn [UMPromising_Sail_outcome_promised_stable
         Sail_outcome_interp Sail_choose Sail_nochoose];
    try contradiction.
  - split.
    + apply reg_read_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - split.
    + apply reg_write_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - match goal with
    | rr : SI.MemReq.t |- _ =>
        destruct rr as [macc addr addr_space size nt]
    end.
    cbn [MemReq_from_sail].
    destruct nt as [|tag].
    + split.
      * eapply UMPromising_mem_read_promised_stable_from_read_code.
        exact Hstable.
      * intros [[]|abort]; exact I.
    + split.
      * apply UMPromising_mem_read_nonzero_tag_promised_stable.
      * intros [[]|abort]; exact I.
  - split.
    + apply mem_write_addr_announce_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - exact I.
  - exact I.
  - destruct bar as [dsb|dmb|[]|[]|[]|[]]; split;
      try apply UMPromising_barrier_dsb_outcome_future_promise_stable_promised;
      try apply barrier_dmb_outcome_future_promise_stable_promised;
      try apply barrier_isb_outcome_future_promise_stable_promised;
      try solve_UMPromising_unsupported_promised_stable;
      intro; exact I.
  - split.
    + apply UMPromising_cache_op_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - split.
    + apply UMPromising_tlbop_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - split.
    + apply UMPromising_take_exception_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - split.
    + apply UMPromising_return_exception_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - split.
    + apply UMPromising_translation_start_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - split.
    + apply UMPromising_translation_end_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - split.
    + apply UMPromising_generic_fail_outcome_future_promise_stable_promised.
    + intros [].
  - split.
    + apply UMPromising_generic_fail_outcome_future_promise_stable_promised.
    + intros [].
  - exact I.
  - split.
    + apply UMPromising_generic_fail_outcome_future_promise_stable_promised.
    + intros [].
  - destruct nondet; destruct ct; cbn [Sail_choose Sail_nochoose].
    all: repeat match goal with
    | |- context[decide (?P)] => destruct (decide P)
    | |- context[match decide ?P with _ => _ end] => destruct (decide P)
    | |- context[if ?x then _ else _] => destruct x
    end.
    all: repeat progress (
      unfold mret, mbind, fmap, mthrow, mcall, mcallM,
        mcall_repl, MCall_SubEff, sub_eff, SubEff_suml, SubEff_sumr,
        iMon_throw, fMon_ret, fMon_bind, fMon_fmap, fMon_call,
        mchoosef, mchoosel, mchoose in *;
      cbn in *).
    all: repeat match goal with
    | H : Empty_set |- _ => destruct H
    | |- imon_future_promise_stable_promised _ _ _ _
           (if decide (?P) then _ else _) =>
        destruct (decide P); cbn
    | |- True => exact I
    | |- _ ∧ _ => split
    | |- ∀ _, _ => intro
    | |- outcome_future_promise_stable_promised _ _ _ (GenericFail _) =>
        apply UMPromising_generic_fail_outcome_future_promise_stable_promised
    end.
  - cbn [mdiscard mchoosel mchoose].
    repeat progress (
      unfold mret, mbind, fmap, mcall, mcallM,
        MCall_SubEff, sub_eff, SubEff_suml, SubEff_sumr,
        fMon_ret, fMon_bind, fMon_fmap, fMon_call in *;
      cbn in *).
    repeat match goal with
    | H : fin 0 |- _ => destruct H
    | |- True => exact I
    | |- ∀ _, _ => intro
    end.
  - exact I.
Qed.

Lemma UMPromising_Sail_promised_stable_from_no_promise_read_code
    tid initmem code msg nondet {eo A} (smon : SI.iMon eo A) :
  UMPromising_read_code_stability tid initmem code msg →
  UMPromising_Sail_no_promise smon →
  UMPromising_Sail_promised_stable tid initmem msg nondet smon.
Proof.
  induction smon as [a|T out k IH]; intros Hstable Hno.
  - exact I.
  - cbn in Hno |- *.
    destruct Hno as [Hout_no Htail_no].
    split.
    + apply UMPromising_Sail_outcome_promised_stable_from_read_code
        with (code := code).
      * exact Hstable.
      * exact Hout_no.
    + intro ret.
      apply IH.
      * exact Hstable.
      * apply Htail_no.
Qed.

Lemma UMPromising_Sail_at_most_one_promise_from_no_promise {eo A}
    (smon : SI.iMon eo A) :
  UMPromising_Sail_no_promise smon →
  UMPromising_Sail_at_most_one_promise smon.
Proof.
  induction smon as [a|T out k IH]; intro Hno_promise.
  - exact I.
  - cbn in Hno_promise |- *.
    destruct Hno_promise as [Hout Htail].
    left.
    split.
    + exact Hout.
    + intro ret.
      apply IH.
      apply Htail.
Qed.

Lemma UMPromising_Sail_no_promise_bind {eo A B}
    (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  UMPromising_Sail_no_promise mon →
  (∀ a, UMPromising_Sail_no_promise (k a)) →
  UMPromising_Sail_no_promise (SI.iMon_bind mon k).
Proof.
  revert B k.
  induction mon as [a|T out kmon IH]; intros B k Hno_promise Hk.
  - cbn.
    apply Hk.
  - cbn in Hno_promise |- *.
    destruct Hno_promise as [Hout Htail].
    split.
    + exact Hout.
    + intro ret.
      eapply IH.
      * apply Htail.
      * exact Hk.
Qed.

Lemma UMPromising_Sail_at_most_one_promise_bind_no_left {eo A B}
    (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  UMPromising_Sail_no_promise mon →
  (∀ a, UMPromising_Sail_at_most_one_promise (k a)) →
  UMPromising_Sail_at_most_one_promise (SI.iMon_bind mon k).
Proof.
  revert B k.
  induction mon as [a|T out kmon IH]; intros B k Hno_promise Hk.
  - cbn.
    apply Hk.
  - cbn in Hno_promise |- *.
    destruct Hno_promise as [Hout Htail].
    left.
    split.
    + exact Hout.
    + intro ret.
      eapply IH.
      * apply Htail.
      * exact Hk.
Qed.

Lemma UMPromising_Sail_at_most_one_promise_bind_no_right {eo A B}
    (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  UMPromising_Sail_at_most_one_promise mon →
  (∀ a, UMPromising_Sail_no_promise (k a)) →
  UMPromising_Sail_at_most_one_promise (SI.iMon_bind mon k).
Proof.
  revert B k.
  induction mon as [a|T out kmon IH]; intros B k Hat_most Hk.
  - cbn.
    apply UMPromising_Sail_at_most_one_promise_from_no_promise.
    apply Hk.
  - cbn in Hat_most |- *.
    destruct Hat_most as [[Hout Htail_at_most]|Htail_no].
    + left.
      split.
      * exact Hout.
      * intro ret.
        eapply IH.
        -- apply Htail_at_most.
        -- exact Hk.
    + right.
      intro ret.
      apply UMPromising_Sail_no_promise_bind.
      * apply Htail_no.
      * exact Hk.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_from_no_promise
    tid initmem msg nondet {eo A} (smon : SI.iMon eo A) :
  UMPromising_Sail_no_promise smon →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet smon.
Proof.
  induction smon as [a|T out k IH]; intro Hno.
  - exact I.
  - cbn in Hno |- *.
    destruct Hno as [_ Htail_no].
    right.
    exact Htail_no.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_bind_no_left
    tid initmem msg nondet {eo A B}
    (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  UMPromising_Sail_no_promise mon →
  UMPromising_Sail_promised_stable
    tid initmem msg nondet mon →
  (∀ a,
    UMPromising_Sail_prefix_promised_stable
      tid initmem msg nondet (k a)) →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (SI.iMon_bind mon k).
Proof.
  revert B k.
  induction mon as [a|T out kmon IH]; intros B k Hno Hstable Hk.
  - cbn.
    apply Hk.
  - cbn in Hno, Hstable |- *.
    destruct Hno as [Hout_no Htail_no].
    destruct Hstable as [Hout_stable Htail_stable].
    left.
    split.
    + exact Hout_no.
    + split.
      * exact Hout_stable.
      * intro ret.
        eapply IH.
        -- apply Htail_no.
        -- apply Htail_stable.
        -- exact Hk.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_bind_no_right
    tid initmem msg nondet {eo A B}
    (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet mon →
  (∀ a, UMPromising_Sail_no_promise (k a)) →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (SI.iMon_bind mon k).
Proof.
  revert B k.
  induction mon as [a|T out kmon IH]; intros B k Hstable Hk.
  - cbn.
    apply UMPromising_Sail_prefix_promised_stable_from_no_promise.
    apply Hk.
  - cbn in Hstable |- *.
    destruct Hstable as
      [[Hout_no [Hout_stable Htail_stable]]|Htail_no].
    + left.
      split.
      * exact Hout_no.
      * split.
        -- exact Hout_stable.
        -- intro ret.
           eapply IH.
           ++ apply Htail_stable.
           ++ exact Hk.
    + right.
      intro ret.
      apply UMPromising_Sail_no_promise_bind.
      * apply Htail_no.
      * exact Hk.
Qed.

Lemma UMPromising_Sail_no_promise_try_catch {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  UMPromising_Sail_no_promise mon →
  (∀ e, UMPromising_Sail_no_promise (h e)) →
  UMPromising_Sail_no_promise (System_types.Defs.try_catch mon h).
Proof.
  induction mon as [a|T out k IH]; intros Hno_promise Hh.
  - exact I.
  - cbn in Hno_promise |- *.
    destruct Hno_promise as [Hout Htail].
    destruct out; cbn in Hout |- *; try contradiction;
      try (split; [exact Hout|];
           intro ret; apply IH; [apply Htail|exact Hh]).
    apply Hh.
Qed.

Lemma UMPromising_Sail_at_most_one_promise_try_catch {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  UMPromising_Sail_at_most_one_promise mon →
  (∀ e, UMPromising_Sail_no_promise (h e)) →
  UMPromising_Sail_at_most_one_promise
    (System_types.Defs.try_catch mon h).
Proof.
  induction mon as [a|T out k IH]; intros Hat_most Hh.
  - exact I.
  - cbn in Hat_most |- *.
    destruct out; cbn in Hat_most |- *;
      try (destruct Hat_most as [[Hout Htail_at_most]|Htail_no];
           [left; split;
            [exact Hout
            |intro ret; apply IH; [apply Htail_at_most|exact Hh]]
           |right; intro ret;
            apply UMPromising_Sail_no_promise_try_catch;
            [apply Htail_no|exact Hh]]).
    apply UMPromising_Sail_at_most_one_promise_from_no_promise.
    apply Hh.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_try_catch_no_left
    tid initmem msg nondet {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  UMPromising_Sail_no_promise mon →
  UMPromising_Sail_promised_stable tid initmem msg nondet mon →
  (∀ e, UMPromising_Sail_no_promise (h e)) →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (System_types.Defs.try_catch mon h).
Proof.
  induction mon as [a|T out k IH]; intros Hno Hstable Hh.
  - exact I.
  - cbn in Hno, Hstable |- *.
    destruct out; cbn in Hno, Hstable |- *;
      try
        (destruct Hno as [Hout_no Htail_no];
         destruct Hstable as [Hout_stable Htail_stable];
         left; split;
         [exact Hout_no
         |split;
          [exact Hout_stable
          |intro ret; apply IH;
           [apply Htail_no|apply Htail_stable|exact Hh]]]).
    all: apply UMPromising_Sail_prefix_promised_stable_from_no_promise;
      apply Hh.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_try_catch_no_right
    tid initmem msg nondet {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  UMPromising_Sail_prefix_promised_stable tid initmem msg nondet mon →
  (∀ e, UMPromising_Sail_no_promise (h e)) →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (System_types.Defs.try_catch mon h).
Proof.
  induction mon as [a|T out k IH]; intros Hstable Hh.
  - exact I.
  - cbn in Hstable |- *.
    destruct out; cbn in Hstable |- *;
      try
        (destruct Hstable as
           [[Hout_no [Hout_stable Htail_stable]]|Htail_no];
         [left; split;
          [exact Hout_no
          |split;
           [exact Hout_stable
           |intro ret; apply IH; [apply Htail_stable|exact Hh]]]
         |right; intro ret;
          apply UMPromising_Sail_no_promise_try_catch;
          [apply Htail_no|exact Hh]]).
    all: apply UMPromising_Sail_prefix_promised_stable_from_no_promise;
      apply Hh.
Qed.

Lemma UMPromising_Sail_no_promise_returnm {A E}
    (a : A) :
  UMPromising_Sail_no_promise (System_types.Defs.returnm (E:=E) a).
Proof. exact I. Qed.

Lemma UMPromising_Sail_no_promise_fail {A E} msg :
  UMPromising_Sail_no_promise (System_types.Defs.fail (A:=A) (E:=E) msg).
Proof.
  cbn [System_types.Defs.fail].
  split; [exact I|].
  intros [].
Qed.

Lemma UMPromising_Sail_no_promise_throw {A E} (e : E) :
  UMPromising_Sail_no_promise (System_types.Defs.throw (A:=A) e).
Proof.
  cbn [System_types.Defs.throw].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_exit {A E} :
  UMPromising_Sail_no_promise
    (System_types.Defs.exit (A:=A) (E:=E) tt).
Proof.
  cbn [System_types.Defs.exit].
  apply UMPromising_Sail_no_promise_fail.
Qed.

Lemma UMPromising_Sail_no_promise_liftR {A R E}
    (mon : System_types.Defs.monad E A) :
  UMPromising_Sail_no_promise mon →
  UMPromising_Sail_no_promise (System_types.Defs.liftR (R:=R) mon).
Proof.
  intro Hmon.
  cbn [System_types.Defs.liftR].
  eapply UMPromising_Sail_no_promise_try_catch.
  - exact Hmon.
  - intro.
    apply UMPromising_Sail_no_promise_throw.
Qed.

Lemma UMPromising_Sail_at_most_one_promise_liftR {A R E}
    (mon : System_types.Defs.monad E A) :
  UMPromising_Sail_at_most_one_promise mon →
  UMPromising_Sail_at_most_one_promise
    (System_types.Defs.liftR (R:=R) mon).
Proof.
  intro Hmon.
  cbn [System_types.Defs.liftR].
  eapply UMPromising_Sail_at_most_one_promise_try_catch.
  - exact Hmon.
  - intro.
    apply UMPromising_Sail_no_promise_throw.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_liftR_no_left
    tid initmem msg nondet {A R E}
    (mon : System_types.Defs.monad E A) :
  UMPromising_Sail_no_promise mon →
  UMPromising_Sail_promised_stable tid initmem msg nondet mon →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (System_types.Defs.liftR (R:=R) mon).
Proof.
  intros Hno Hstable.
  cbn [System_types.Defs.liftR].
  eapply UMPromising_Sail_prefix_promised_stable_try_catch_no_left.
  - exact Hno.
  - exact Hstable.
  - intro.
    apply UMPromising_Sail_no_promise_throw.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_liftR_no_right
    tid initmem msg nondet {A R E}
    (mon : System_types.Defs.monad E A) :
  UMPromising_Sail_prefix_promised_stable tid initmem msg nondet mon →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (System_types.Defs.liftR (R:=R) mon).
Proof.
  intro Hstable.
  cbn [System_types.Defs.liftR].
  eapply UMPromising_Sail_prefix_promised_stable_try_catch_no_right.
  - exact Hstable.
  - intro.
    apply UMPromising_Sail_no_promise_throw.
Qed.

Lemma UMPromising_Sail_no_promise_catch_early_return {A E}
    (mon : System_types.Defs.monadR A E A) :
  UMPromising_Sail_no_promise mon →
  UMPromising_Sail_no_promise
    (System_types.Defs.catch_early_return mon).
Proof.
  intro Hmon.
  cbn [System_types.Defs.catch_early_return].
  eapply UMPromising_Sail_no_promise_try_catch.
  - exact Hmon.
  - intros [a|e].
    + apply UMPromising_Sail_no_promise_returnm.
    + apply UMPromising_Sail_no_promise_throw.
Qed.

Lemma UMPromising_Sail_at_most_one_promise_catch_early_return {A E}
    (mon : System_types.Defs.monadR A E A) :
  UMPromising_Sail_at_most_one_promise mon →
  UMPromising_Sail_at_most_one_promise
    (System_types.Defs.catch_early_return mon).
Proof.
  intro Hmon.
  cbn [System_types.Defs.catch_early_return].
  eapply UMPromising_Sail_at_most_one_promise_try_catch.
  - exact Hmon.
  - intros [a|e].
    + apply UMPromising_Sail_no_promise_returnm.
    + apply UMPromising_Sail_no_promise_throw.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_catch_early_return_no_right
    tid initmem msg nondet {A E}
    (mon : System_types.Defs.monadR A E A) :
  UMPromising_Sail_prefix_promised_stable tid initmem msg nondet mon →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (System_types.Defs.catch_early_return mon).
Proof.
  intro Hstable.
  cbn [System_types.Defs.catch_early_return].
  eapply UMPromising_Sail_prefix_promised_stable_try_catch_no_right.
  - exact Hstable.
  - intros [a|e].
    + apply UMPromising_Sail_no_promise_returnm.
    + apply UMPromising_Sail_no_promise_throw.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_catch_early_return_no_left
    tid initmem msg nondet {A E}
    (mon : System_types.Defs.monadR A E A) :
  UMPromising_Sail_no_promise mon →
  UMPromising_Sail_promised_stable tid initmem msg nondet mon →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (System_types.Defs.catch_early_return mon).
Proof.
  intros Hno Hstable.
  cbn [System_types.Defs.catch_early_return].
  eapply UMPromising_Sail_prefix_promised_stable_try_catch_no_left.
  - exact Hno.
  - exact Hstable.
  - intros [a|e].
    + apply UMPromising_Sail_no_promise_returnm.
    + apply UMPromising_Sail_no_promise_throw.
Qed.

Lemma UMPromising_Sail_no_promise_bind0 {A E}
    (mon : System_types.Defs.monad E unit)
    (tail : System_types.Defs.monad E A) :
  UMPromising_Sail_no_promise mon →
  UMPromising_Sail_no_promise tail →
  UMPromising_Sail_no_promise (System_types.Defs.bind0 mon tail).
Proof.
  intros Hmon Htail.
  cbn [System_types.Defs.bind0 System_types.Defs.bind].
  apply UMPromising_Sail_no_promise_bind.
  - exact Hmon.
  - intro.
    exact Htail.
Qed.

Lemma UMPromising_Sail_at_most_one_promise_bind0_no_left {A E}
    (mon : System_types.Defs.monad E unit)
    (tail : System_types.Defs.monad E A) :
  UMPromising_Sail_no_promise mon →
  UMPromising_Sail_at_most_one_promise tail →
  UMPromising_Sail_at_most_one_promise
    (System_types.Defs.bind0 mon tail).
Proof.
  intros Hmon Htail.
  cbn [System_types.Defs.bind0 System_types.Defs.bind].
  eapply UMPromising_Sail_at_most_one_promise_bind_no_left.
  - exact Hmon.
  - intro.
    exact Htail.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_bind0_no_left
    tid initmem msg nondet {A E}
    (mon : System_types.Defs.monad E unit)
    (tail : System_types.Defs.monad E A) :
  UMPromising_Sail_no_promise mon →
  UMPromising_Sail_promised_stable tid initmem msg nondet mon →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet tail →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (System_types.Defs.bind0 mon tail).
Proof.
  intros Hmon_no Hmon_stable Htail.
  cbn [System_types.Defs.bind0 System_types.Defs.bind].
  eapply UMPromising_Sail_prefix_promised_stable_bind_no_left.
  - exact Hmon_no.
  - exact Hmon_stable.
  - intro.
    exact Htail.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_bind0_no_right
    tid initmem msg nondet {A E}
    (mon : System_types.Defs.monad E unit)
    (tail : System_types.Defs.monad E A) :
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet mon →
  UMPromising_Sail_no_promise tail →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (System_types.Defs.bind0 mon tail).
Proof.
  intros Hmon Htail_no.
  cbn [System_types.Defs.bind0 System_types.Defs.bind].
  eapply UMPromising_Sail_prefix_promised_stable_bind_no_right.
  - exact Hmon.
  - intro.
    exact Htail_no.
Qed.

Lemma UMPromising_Sail_no_promise_read_reg {E}
    (reg : System_types.Arch.reg) :
  UMPromising_Sail_no_promise
    (System_types.Defs.read_reg (e:=E) reg).
Proof.
  cbn [System_types.Defs.read_reg].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_write_reg {E}
    (reg : System_types.Arch.reg) (v : System_types.Arch.reg_type reg) :
  UMPromising_Sail_no_promise
    (System_types.Defs.write_reg (e:=E) reg v).
Proof.
  cbn [System_types.Defs.write_reg].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_read_reg_ref {A E}
    (ref : Values.register_ref A) :
  UMPromising_Sail_no_promise
    (System_types.Defs.read_reg_ref (e:=E) ref).
Proof.
  cbn [System_types.Defs.read_reg_ref].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_reg_deref {A E}
    (ref : Values.register_ref A) :
  UMPromising_Sail_no_promise
    (System_types.Defs.reg_deref (e:=E) ref).
Proof.
  cbn [System_types.Defs.reg_deref].
  apply UMPromising_Sail_no_promise_read_reg_ref.
Qed.

Lemma UMPromising_Sail_no_promise_write_reg_ref {A E}
    (ref : Values.register_ref A) (v : A) :
  UMPromising_Sail_no_promise
    (System_types.Defs.write_reg_ref (e:=E) ref v).
Proof.
  cbn [System_types.Defs.write_reg_ref].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_sail_mem_read {E n nt}
    req :
  UMPromising_Sail_no_promise
    (System_types.Defs.sail_mem_read (e:=E) (n:=n) (nt:=nt) req).
Proof.
  cbn [System_types.Defs.sail_mem_read].
  split; [exact I|].
  intros [[data tags]|abort].
  all: exact I.
Qed.

Lemma UMPromising_Sail_at_most_one_promise_sail_mem_write {E n nt}
    req value tags :
  UMPromising_Sail_at_most_one_promise
    (System_types.Defs.sail_mem_write
       (e:=E) (n:=n) (nt:=nt) req value tags).
Proof.
  cbn [System_types.Defs.sail_mem_write].
  right.
  intros [[]|abort].
  all: exact I.
Qed.

Lemma UMPromising_Sail_no_promise_sail_barrier {E} b :
  UMPromising_Sail_no_promise
    (System_types.Defs.sail_barrier (e:=E) b).
Proof.
  cbn [System_types.Defs.sail_barrier].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_sail_translation_start {E} ts :
  UMPromising_Sail_no_promise
    (System_types.Defs.sail_translation_start (e:=E) ts).
Proof.
  cbn [System_types.Defs.sail_translation_start].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_sail_translation_end {E} te :
  UMPromising_Sail_no_promise
    (System_types.Defs.sail_translation_end (e:=E) te).
Proof.
  cbn [System_types.Defs.sail_translation_end].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_sail_take_exception {E} exn :
  UMPromising_Sail_no_promise
    (System_types.Defs.sail_take_exception (e:=E) exn).
Proof.
  cbn [System_types.Defs.sail_take_exception].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_sail_tlbi {E} tlbi :
  UMPromising_Sail_no_promise
    (System_types.Defs.sail_tlbi (e:=E) tlbi).
Proof.
  cbn [System_types.Defs.sail_tlbi].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_choose_range {E} descr lo hi :
  UMPromising_Sail_no_promise
    (System_types.Defs.choose_range (E:=E) descr lo hi).
Proof.
  cbn [System_types.Defs.choose_range].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_choose_from_list {A E} descr
    (xs : list A) :
  UMPromising_Sail_no_promise
    (System_types.Defs.choose_from_list (E:=E) descr xs).
Proof.
  cbn [System_types.Defs.choose_from_list System_types.Defs.bind].
  apply UMPromising_Sail_no_promise_bind.
  - apply UMPromising_Sail_no_promise_choose_range.
  - intro idx.
    destruct (nth_error xs (Z.to_nat idx)).
    + apply UMPromising_Sail_no_promise_returnm.
    + apply UMPromising_Sail_no_promise_fail.
Qed.

Lemma UMPromising_Sail_no_promise_internal_pick {A E}
    (xs : list A) :
  UMPromising_Sail_no_promise
    (System_types.Defs.internal_pick (e:=E) xs).
Proof.
  cbn [System_types.Defs.internal_pick].
  apply UMPromising_Sail_no_promise_choose_from_list.
Qed.

Lemma UMPromising_Sail_no_promise_foreach_ZM_up' {E Vars}
    from to step fuel (vars : Vars)
    (body : Z → Vars → System_types.Defs.monad E Vars) :
  (∀ z vars, UMPromising_Sail_no_promise (body z vars)) →
  UMPromising_Sail_no_promise
    (System_types.Defs.foreach_ZM_up' from to step fuel vars body).
Proof.
  revert from vars.
  induction fuel as [|fuel IH]; intros from vars Hbody.
  - cbn [System_types.Defs.foreach_ZM_up'].
    destruct (from <=? to); apply UMPromising_Sail_no_promise_returnm.
  - cbn [System_types.Defs.foreach_ZM_up'].
    destruct (from <=? to).
    + cbn [System_types.Defs.bind].
      apply UMPromising_Sail_no_promise_bind.
      * apply Hbody.
      * intro vars'.
        apply IH.
        apply Hbody.
    + apply UMPromising_Sail_no_promise_returnm.
Qed.

Lemma UMPromising_Sail_no_promise_foreach_ZM_up {E Vars}
    from to step (vars : Vars)
    (body : Z → Vars → System_types.Defs.monad E Vars) :
  (∀ z vars, UMPromising_Sail_no_promise (body z vars)) →
  UMPromising_Sail_no_promise
    (System_types.Defs.foreach_ZM_up from to step vars body).
Proof.
  cbn [System_types.Defs.foreach_ZM_up].
  apply UMPromising_Sail_no_promise_foreach_ZM_up'.
Qed.

Ltac UMPromising_Sail_simpl :=
	  cbn [System_types.Defs.returnm System_types.Defs.fail
	       System_types.Defs.throw System_types.Defs.exit
	       System_types.Defs.early_return
	       System_types.Defs.assert_exp' System_types.Defs.sail_mem_read
       System_types.Defs.sail_mem_write System_types.Defs.sail_barrier
	       System_types.Defs.sail_translation_start
	       System_types.Defs.sail_translation_end
	       System_types.Defs.sail_take_exception System_types.Defs.sail_tlbi
	       System_types.Defs.choose_range System_types.Defs.choose_from_list
	       System_types.Defs.internal_pick System_types.Defs.read_reg
	       System_types.Defs.write_reg System_types.Defs.read_reg_ref
	       System_types.Defs.reg_deref System_types.Defs.write_reg_ref
	       System_types.Defs.foreach_ZM_up System_types.Defs.foreach_ZM_up'
	       System_types.Defs.autocast_m
	       System_types.returnM System_types.returnR
	       System_types.Defs.returnR] in *;
  unfold System_types.returnM, System_types.returnR,
    System_types.Defs.returnR, System_types.Defs.early_return,
    System_types.Defs.autocast_m in *;
  unfold System_types.Defs.bind, System_types.Defs.bind0 in *.

Ltac solve_UMPromising_Sail_no_promise :=
  lazymatch goal with
	  | |- True => exact I
	  | |- UMPromising_Sail_no_promise
	        (System_types.Interface.Ret _) =>
	      exact I
	  | |- UMPromising_Sail_no_promise
	        (System_types.Defs.returnR _ _) =>
	      exact I
	  | |- UMPromising_Sail_no_promise
	        (System_types.Defs.assert_exp' ?b _) =>
	      destruct b;
	      [apply UMPromising_Sail_no_promise_returnm
	      |apply UMPromising_Sail_no_promise_fail]
	  | |- UMPromising_Sail_no_promise
	        (System_types.Defs.assert_exp ?b _) =>
	      destruct b;
	      [apply UMPromising_Sail_no_promise_returnm
	      |apply UMPromising_Sail_no_promise_fail]
	  | |- _ ∧ _ =>
	      split; solve_UMPromising_Sail_no_promise
	  | |- ∀ _, _ =>
	      intro; solve_UMPromising_Sail_no_promise
	  | |- UMPromising_Sail_no_promise
	        (System_types.Defs.bind _ _) =>
	      unfold System_types.Defs.bind;
	      eapply UMPromising_Sail_no_promise_bind;
	      [solve_UMPromising_Sail_no_promise
	      |intro; solve_UMPromising_Sail_no_promise]
	  | |- UMPromising_Sail_no_promise
	        (System_types.Defs.bind0 _ _) =>
	      eapply UMPromising_Sail_no_promise_bind0;
	      [solve_UMPromising_Sail_no_promise
	      |solve_UMPromising_Sail_no_promise]
	  | |- UMPromising_Sail_no_promise
	        (System_types.Interface.iMon_bind _ _) =>
	      eapply UMPromising_Sail_no_promise_bind;
      [solve_UMPromising_Sail_no_promise
      |intro; solve_UMPromising_Sail_no_promise]
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.try_catch _ _) =>
      eapply UMPromising_Sail_no_promise_try_catch;
      [solve_UMPromising_Sail_no_promise
      |intro; solve_UMPromising_Sail_no_promise]
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.liftR _) =>
      apply UMPromising_Sail_no_promise_liftR;
      solve_UMPromising_Sail_no_promise
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.catch_early_return _) =>
      apply UMPromising_Sail_no_promise_catch_early_return;
      solve_UMPromising_Sail_no_promise
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.returnm _) =>
      apply UMPromising_Sail_no_promise_returnm
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.fail _) =>
      apply UMPromising_Sail_no_promise_fail
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.throw _) =>
      apply UMPromising_Sail_no_promise_throw
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.exit _) =>
      apply UMPromising_Sail_no_promise_exit
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.read_reg _) =>
      apply UMPromising_Sail_no_promise_read_reg
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.write_reg _ _) =>
      apply UMPromising_Sail_no_promise_write_reg
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.read_reg_ref _) =>
      apply UMPromising_Sail_no_promise_read_reg_ref
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.reg_deref _) =>
      apply UMPromising_Sail_no_promise_reg_deref
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.write_reg_ref _ _) =>
      apply UMPromising_Sail_no_promise_write_reg_ref
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.sail_mem_read _) =>
      apply UMPromising_Sail_no_promise_sail_mem_read
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.sail_barrier _) =>
      apply UMPromising_Sail_no_promise_sail_barrier
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.sail_translation_start _) =>
      apply UMPromising_Sail_no_promise_sail_translation_start
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.sail_translation_end _) =>
      apply UMPromising_Sail_no_promise_sail_translation_end
	  | |- UMPromising_Sail_no_promise
	        (System_types.Defs.sail_take_exception _) =>
	      apply UMPromising_Sail_no_promise_sail_take_exception
	  | |- UMPromising_Sail_no_promise
	        (System_types.Defs.sail_tlbi _) =>
	      apply UMPromising_Sail_no_promise_sail_tlbi
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.choose_range _ _ _) =>
      apply UMPromising_Sail_no_promise_choose_range
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.choose_from_list _ _) =>
      apply UMPromising_Sail_no_promise_choose_from_list
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.internal_pick _) =>
      apply UMPromising_Sail_no_promise_internal_pick
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.foreach_ZM_up _ _ _ _ _) =>
      apply UMPromising_Sail_no_promise_foreach_ZM_up;
      intros; solve_UMPromising_Sail_no_promise
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_UMPromising_Sail_no_promise
  | |- context[if ?x then _ else _] =>
      destruct x; solve_UMPromising_Sail_no_promise
	  | |- UMPromising_Sail_no_promise _ =>
	      progress UMPromising_Sail_simpl;
	      solve_UMPromising_Sail_no_promise
	  end.

Ltac solve_UMPromising_Sail_at_most_one_promise :=
	  lazymatch goal with
	  | |- UMPromising_Sail_at_most_one_promise
	        (System_types.Interface.Ret _) =>
	      exact I
	  | |- UMPromising_Sail_at_most_one_promise
	        (System_types.Defs.returnR _ _) =>
	      exact I
	  | |- UMPromising_Sail_at_most_one_promise
	        (System_types.Defs.bind _ _) =>
	      unfold System_types.Defs.bind;
	      first
	        [eapply UMPromising_Sail_at_most_one_promise_bind_no_left;
	         [solve_UMPromising_Sail_no_promise
	         |intro; solve_UMPromising_Sail_at_most_one_promise]
	        |eapply UMPromising_Sail_at_most_one_promise_bind_no_right;
	         [solve_UMPromising_Sail_at_most_one_promise
	         |intro; solve_UMPromising_Sail_no_promise]]
	  | |- UMPromising_Sail_at_most_one_promise
	        (System_types.Defs.bind0 _ _) =>
	      eapply UMPromising_Sail_at_most_one_promise_bind0_no_left;
	      [solve_UMPromising_Sail_no_promise
	      |solve_UMPromising_Sail_at_most_one_promise]
	  | |- UMPromising_Sail_at_most_one_promise
	        (System_types.Interface.iMon_bind _ _) =>
	      first
        [eapply UMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_UMPromising_Sail_no_promise
         |intro; solve_UMPromising_Sail_at_most_one_promise]
        |eapply UMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_UMPromising_Sail_at_most_one_promise
         |intro; solve_UMPromising_Sail_no_promise]]
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.try_catch _ _) =>
      eapply UMPromising_Sail_at_most_one_promise_try_catch;
      [solve_UMPromising_Sail_at_most_one_promise
      |intro; solve_UMPromising_Sail_no_promise]
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.liftR _) =>
      apply UMPromising_Sail_at_most_one_promise_liftR;
      solve_UMPromising_Sail_at_most_one_promise
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.catch_early_return _) =>
      apply UMPromising_Sail_at_most_one_promise_catch_early_return;
      solve_UMPromising_Sail_at_most_one_promise
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.sail_mem_write _ _ _) =>
      apply UMPromising_Sail_at_most_one_promise_sail_mem_write
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_UMPromising_Sail_at_most_one_promise
  | |- context[if ?x then _ else _] =>
      destruct x; solve_UMPromising_Sail_at_most_one_promise
  | |- UMPromising_Sail_at_most_one_promise _ =>
      first
        [progress UMPromising_Sail_simpl;
         solve_UMPromising_Sail_at_most_one_promise
        |apply UMPromising_Sail_at_most_one_promise_from_no_promise;
         solve_UMPromising_Sail_no_promise]
  end.

Lemma UMPromising_Sail_no_promise_create_writeAccessDescriptor :
  UMPromising_Sail_no_promise
    (System.create_writeAccessDescriptor tt).
Proof.
  unfold System.create_writeAccessDescriptor, System_types.Defs.bind.
  apply UMPromising_Sail_no_promise_bind.
  - apply UMPromising_Sail_no_promise_read_reg.
  - intro.
    apply UMPromising_Sail_no_promise_returnm.
Qed.

Lemma UMPromising_Sail_no_promise_create_readAccessDescriptor :
  UMPromising_Sail_no_promise
    (System.create_readAccessDescriptor tt).
Proof.
  unfold System.create_readAccessDescriptor, System_types.Defs.bind.
  apply UMPromising_Sail_no_promise_bind.
  - apply UMPromising_Sail_no_promise_read_reg.
  - intro.
    apply UMPromising_Sail_no_promise_returnm.
Qed.

Lemma UMPromising_Sail_no_promise_create_iFetchAccessDescriptor :
  UMPromising_Sail_no_promise
    (System.create_iFetchAccessDescriptor tt).
Proof.
  unfold System.create_iFetchAccessDescriptor, System_types.Defs.bind.
  apply UMPromising_Sail_no_promise_bind.
  - apply UMPromising_Sail_no_promise_read_reg.
  - intro.
    apply UMPromising_Sail_no_promise_returnm.
Qed.

Lemma UMPromising_Sail_no_promise_rX n :
  UMPromising_Sail_no_promise (System.rX n).
Proof.
  unfold System.rX.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_wX n value :
  UMPromising_Sail_no_promise (System.wX n value).
Proof.
  unfold System.wX.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_rPC :
  UMPromising_Sail_no_promise (System.rPC tt).
Proof.
  unfold System.rPC.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_wPC pc :
  UMPromising_Sail_no_promise (System.wPC pc).
Proof.
  unfold System.wPC.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_read_memory N addr accdesc :
  UMPromising_Sail_no_promise (System.read_memory N addr accdesc).
Proof.
  unfold System.read_memory.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_iFetch addr accdesc :
  UMPromising_Sail_no_promise (System.iFetch addr accdesc).
Proof.
  unfold System.iFetch.
  apply UMPromising_Sail_no_promise_read_memory.
Qed.

Lemma UMPromising_Sail_no_promise_rMem N addr accdesc :
  UMPromising_Sail_no_promise (System.rMem N addr accdesc).
Proof.
  unfold System.rMem.
  apply UMPromising_Sail_no_promise_read_memory.
Qed.

Lemma UMPromising_Sail_at_most_one_promise_wMem N addr value accdesc :
  UMPromising_Sail_at_most_one_promise
    (System.wMem N addr value accdesc).
Proof.
  unfold System.wMem.
  solve_UMPromising_Sail_at_most_one_promise.
Qed.

Lemma UMPromising_Sail_no_promise_dataMemoryBarrier domain types :
  UMPromising_Sail_no_promise (System.dataMemoryBarrier domain types).
Proof.
  unfold System.dataMemoryBarrier.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_dataSynchronizationBarrer
    domain types :
  UMPromising_Sail_no_promise
    (System.dataSynchronizationBarrer domain types).
Proof.
  unfold System.dataSynchronizationBarrer.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_instructionSynchronizationBarrier :
  UMPromising_Sail_no_promise (System.instructionSynchronizationBarrier tt).
Proof.
  unfold System.instructionSynchronizationBarrier.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_reportTLBI op addr asid :
  UMPromising_Sail_no_promise (System.reportTLBI op addr asid).
Proof.
  unfold System.reportTLBI.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_wW n value :
  UMPromising_Sail_no_promise (System.wW n value).
Proof.
  unfold System.wW.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_rW n :
  UMPromising_Sail_no_promise (System.rW n).
Proof.
  unfold System.rW.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_rXS n size :
  UMPromising_Sail_no_promise (System.rXS n size).
Proof.
  unfold System.rXS.
  destruct (Z.eqb size 64);
    unfold System_types.Defs.autocast_m;
    apply UMPromising_Sail_no_promise_bind.
  - apply UMPromising_Sail_no_promise_rX.
  - intro.
    apply UMPromising_Sail_no_promise_returnm.
  - apply UMPromising_Sail_no_promise_rW.
  - intro.
    apply UMPromising_Sail_no_promise_returnm.
Qed.

Lemma UMPromising_Sail_no_promise_wXS n size value :
  UMPromising_Sail_no_promise (System.wXS n size value).
Proof.
  unfold System.wXS.
  destruct (Z.eqb size 64).
  - apply UMPromising_Sail_no_promise_wX.
  - apply UMPromising_Sail_no_promise_wW.
Qed.

Lemma UMPromising_Sail_no_promise_get_translation_base_address varange :
  UMPromising_Sail_no_promise
    (System.get_translation_base_address varange).
Proof.
  unfold System.get_translation_base_address.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_ASID_read :
  UMPromising_Sail_no_promise (System.ASID_read tt).
Proof.
  unfold System.ASID_read.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_create_AccessDescriptorTTW
    toplevel varange :
  UMPromising_Sail_no_promise
    (System.create_AccessDescriptorTTW toplevel varange).
Proof.
  unfold System.create_AccessDescriptorTTW.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_pgt_walk va accdesc :
  UMPromising_Sail_no_promise (System.pgt_walk va accdesc).
Proof.
  unfold System.pgt_walk, System.get_translation_base_address,
    System.create_AccessDescriptorTTW, System.read_memory.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_take_exception target_el fault :
  UMPromising_Sail_no_promise
    (System.take_exception target_el fault).
Proof.
  unfold System.take_exception.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_handle_fault addrdesc :
  UMPromising_Sail_no_promise (System.handle_fault addrdesc).
Proof.
  unfold System.handle_fault, System.take_exception.
  solve_UMPromising_Sail_no_promise.
Qed.

Ltac solve_UMPromising_Sail_no_promise_addr :=
  lazymatch goal with
  | |- UMPromising_Sail_no_promise
        (System.get_translation_base_address _) =>
      apply UMPromising_Sail_no_promise_get_translation_base_address
  | |- UMPromising_Sail_no_promise (System.ASID_read _) =>
      apply UMPromising_Sail_no_promise_ASID_read
  | |- UMPromising_Sail_no_promise
        (System.create_AccessDescriptorTTW _ _) =>
      apply UMPromising_Sail_no_promise_create_AccessDescriptorTTW
  | |- UMPromising_Sail_no_promise (System.pgt_walk _ _) =>
      apply UMPromising_Sail_no_promise_pgt_walk
  | |- UMPromising_Sail_no_promise (System.take_exception _ _) =>
      apply UMPromising_Sail_no_promise_take_exception
  | |- UMPromising_Sail_no_promise (System.handle_fault _) =>
      apply UMPromising_Sail_no_promise_handle_fault
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      eapply UMPromising_Sail_no_promise_bind;
      [solve_UMPromising_Sail_no_promise_addr
      |intro; solve_UMPromising_Sail_no_promise_addr]
  | |- UMPromising_Sail_no_promise
        (System_types.Interface.iMon_bind _ _) =>
      eapply UMPromising_Sail_no_promise_bind;
      [solve_UMPromising_Sail_no_promise_addr
      |intro; solve_UMPromising_Sail_no_promise_addr]
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.bind0 _ _) =>
      eapply UMPromising_Sail_no_promise_bind0;
      [solve_UMPromising_Sail_no_promise_addr
      |solve_UMPromising_Sail_no_promise_addr]
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.try_catch _ _) =>
      eapply UMPromising_Sail_no_promise_try_catch;
      [solve_UMPromising_Sail_no_promise_addr
      |intro; solve_UMPromising_Sail_no_promise_addr]
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.liftR _) =>
      apply UMPromising_Sail_no_promise_liftR;
      solve_UMPromising_Sail_no_promise_addr
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.catch_early_return _) =>
      apply UMPromising_Sail_no_promise_catch_early_return;
      solve_UMPromising_Sail_no_promise_addr
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_UMPromising_Sail_no_promise_addr
  | |- context[if ?x then _ else _] =>
      destruct x; solve_UMPromising_Sail_no_promise_addr
  | _ => solve_UMPromising_Sail_no_promise
  end.

Lemma UMPromising_Sail_no_promise_translate_address va accdesc :
  UMPromising_Sail_no_promise (System.translate_address va accdesc).
Proof.
  unfold System.translate_address.
  solve_UMPromising_Sail_no_promise_addr.
Qed.

Lemma UMPromising_Sail_no_promise_decode_bitwise_op opc :
  UMPromising_Sail_no_promise (System.decode_bitwise_op opc).
Proof.
  unfold System.decode_bitwise_op.
  repeat match goal with
  | |- context[if ?b then _ else _] => destruct b
  end;
    try apply UMPromising_Sail_no_promise_returnm;
    unfold System.fail;
    solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_decode_bitmask N imms immr :
  UMPromising_Sail_no_promise (System.decode_bitmask N imms immr).
Proof.
  unfold System.decode_bitmask.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_decode v :
  UMPromising_Sail_no_promise (System.decode v).
Proof.
  unfold System.decode, System.decode_bitwise_op, System.decode_bitmask,
    System.fail.
  solve_UMPromising_Sail_no_promise.
Qed.

Ltac solve_UMPromising_Sail_no_promise_exec :=
  lazymatch goal with
  | |- UMPromising_Sail_no_promise (System.rX _) =>
      apply UMPromising_Sail_no_promise_rX
  | |- UMPromising_Sail_no_promise (System.wX _ _) =>
      apply UMPromising_Sail_no_promise_wX
  | |- UMPromising_Sail_no_promise (System.rW _) =>
      apply UMPromising_Sail_no_promise_rW
  | |- UMPromising_Sail_no_promise (System.wW _ _) =>
      apply UMPromising_Sail_no_promise_wW
  | |- UMPromising_Sail_no_promise (System.rXS _ _) =>
      apply UMPromising_Sail_no_promise_rXS
  | |- UMPromising_Sail_no_promise (System.wXS _ _ _) =>
      apply UMPromising_Sail_no_promise_wXS
  | |- UMPromising_Sail_no_promise (System.rPC _) =>
      apply UMPromising_Sail_no_promise_rPC
  | |- UMPromising_Sail_no_promise (System.wPC _) =>
      apply UMPromising_Sail_no_promise_wPC
  | |- UMPromising_Sail_no_promise
        (System.create_writeAccessDescriptor _) =>
      apply UMPromising_Sail_no_promise_create_writeAccessDescriptor
  | |- UMPromising_Sail_no_promise
        (System.create_readAccessDescriptor _) =>
      apply UMPromising_Sail_no_promise_create_readAccessDescriptor
  | |- UMPromising_Sail_no_promise
        (System.create_iFetchAccessDescriptor _) =>
      apply UMPromising_Sail_no_promise_create_iFetchAccessDescriptor
  | |- UMPromising_Sail_no_promise (System.read_memory _ _ _) =>
      apply UMPromising_Sail_no_promise_read_memory
  | |- UMPromising_Sail_no_promise (System.iFetch _ _) =>
      apply UMPromising_Sail_no_promise_iFetch
  | |- UMPromising_Sail_no_promise (System.rMem _ _ _) =>
      apply UMPromising_Sail_no_promise_rMem
  | |- UMPromising_Sail_no_promise (System.dataMemoryBarrier _ _) =>
      apply UMPromising_Sail_no_promise_dataMemoryBarrier
  | |- UMPromising_Sail_no_promise
        (System.dataSynchronizationBarrer _ _) =>
      apply UMPromising_Sail_no_promise_dataSynchronizationBarrer
  | |- UMPromising_Sail_no_promise
        (System.instructionSynchronizationBarrier ?u) =>
      destruct u;
      apply UMPromising_Sail_no_promise_instructionSynchronizationBarrier
  | |- UMPromising_Sail_no_promise (System.reportTLBI _ _ _) =>
      apply UMPromising_Sail_no_promise_reportTLBI
  | |- UMPromising_Sail_no_promise (System.take_exception _ _) =>
      apply UMPromising_Sail_no_promise_take_exception
  | |- UMPromising_Sail_no_promise (System.handle_fault _) =>
      apply UMPromising_Sail_no_promise_handle_fault
  | |- UMPromising_Sail_no_promise (System.translate_address _ _) =>
      apply UMPromising_Sail_no_promise_translate_address
  | |- UMPromising_Sail_no_promise (System.decode_bitwise_op _) =>
      apply UMPromising_Sail_no_promise_decode_bitwise_op
  | |- UMPromising_Sail_no_promise (System.decode_bitmask _ _ _) =>
      apply UMPromising_Sail_no_promise_decode_bitmask
  | |- UMPromising_Sail_no_promise (System.decode _) =>
      apply UMPromising_Sail_no_promise_decode
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      eapply UMPromising_Sail_no_promise_bind;
      [solve_UMPromising_Sail_no_promise_exec
      |intro; solve_UMPromising_Sail_no_promise_exec]
  | |- UMPromising_Sail_no_promise
        (System_types.Interface.iMon_bind _ _) =>
      eapply UMPromising_Sail_no_promise_bind;
      [solve_UMPromising_Sail_no_promise_exec
      |intro; solve_UMPromising_Sail_no_promise_exec]
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.bind0 _ _) =>
      eapply UMPromising_Sail_no_promise_bind0;
      [solve_UMPromising_Sail_no_promise_exec
      |solve_UMPromising_Sail_no_promise_exec]
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.liftR _) =>
      apply UMPromising_Sail_no_promise_liftR;
      solve_UMPromising_Sail_no_promise_exec
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.catch_early_return _) =>
      apply UMPromising_Sail_no_promise_catch_early_return;
      solve_UMPromising_Sail_no_promise_exec
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_UMPromising_Sail_no_promise_exec
  | |- context[if ?x then _ else _] =>
      destruct x; solve_UMPromising_Sail_no_promise_exec
  | _ => solve_UMPromising_Sail_no_promise
  end.

Ltac solve_UMPromising_Sail_at_most_one_promise_exec :=
  lazymatch goal with
  | |- UMPromising_Sail_at_most_one_promise (System.wMem _ _ _ _) =>
      apply UMPromising_Sail_at_most_one_promise_wMem
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      first
        [eapply UMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_UMPromising_Sail_no_promise_exec
         |intro; solve_UMPromising_Sail_at_most_one_promise_exec]
        |eapply UMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_UMPromising_Sail_at_most_one_promise_exec
         |intro; solve_UMPromising_Sail_no_promise_exec]]
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Interface.iMon_bind _ _) =>
      first
        [eapply UMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_UMPromising_Sail_no_promise_exec
         |intro; solve_UMPromising_Sail_at_most_one_promise_exec]
        |eapply UMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_UMPromising_Sail_at_most_one_promise_exec
         |intro; solve_UMPromising_Sail_no_promise_exec]]
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind0 _ _) =>
      eapply UMPromising_Sail_at_most_one_promise_bind0_no_left;
      [solve_UMPromising_Sail_no_promise_exec
      |solve_UMPromising_Sail_at_most_one_promise_exec]
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.liftR _) =>
      apply UMPromising_Sail_at_most_one_promise_liftR;
      solve_UMPromising_Sail_at_most_one_promise_exec
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.catch_early_return _) =>
      apply UMPromising_Sail_at_most_one_promise_catch_early_return;
      solve_UMPromising_Sail_at_most_one_promise_exec
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_UMPromising_Sail_at_most_one_promise_exec
  | |- context[if ?x then _ else _] =>
      destruct x; solve_UMPromising_Sail_at_most_one_promise_exec
  | _ =>
      apply UMPromising_Sail_at_most_one_promise_from_no_promise;
      solve_UMPromising_Sail_no_promise_exec
  end.

Lemma UMPromising_Sail_no_promise_execute_TLBInvalidation op t :
  UMPromising_Sail_no_promise
    (System.execute_TLBInvalidation op t).
Proof.
  unfold System.execute_TLBInvalidation.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_SupervisorCall imm16 :
  UMPromising_Sail_no_promise (System.execute_SupervisorCall imm16).
Proof.
  unfold System.execute_SupervisorCall.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_Sub sf d n op :
  UMPromising_Sail_no_promise (System.execute_Sub sf d n op).
Proof.
  unfold System.execute_Sub.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_at_most_one_promise_execute_Store
    size t n op :
  UMPromising_Sail_at_most_one_promise
    (System.execute_Store size t n op).
Proof.
  unfold System.execute_Store.
  solve_UMPromising_Sail_at_most_one_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_Nop :
  UMPromising_Sail_no_promise (System.execute_Nop tt).
Proof.
  unfold System.execute_Nop.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_Movz sf d imm hw :
  UMPromising_Sail_no_promise (System.execute_Movz sf d imm hw).
Proof.
  unfold System.execute_Movz.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_Load size t n op :
  UMPromising_Sail_no_promise (System.execute_Load size t n op).
Proof.
  unfold System.execute_Load.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_ISB :
  UMPromising_Sail_no_promise
    (System.execute_InstructionSynchronizationBarrier tt).
Proof.
  unfold System.execute_InstructionSynchronizationBarrier.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_ExceptionReturn :
  UMPromising_Sail_no_promise (System.execute_ExceptionReturn tt).
Proof.
  unfold System.execute_ExceptionReturn.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_DSB domain types :
  UMPromising_Sail_no_promise
    (System.execute_DataSynchronizationBarrier domain types).
Proof.
  unfold System.execute_DataSynchronizationBarrier.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_DMB domain types :
  UMPromising_Sail_no_promise
    (System.execute_DataMemoryBarrier domain types).
Proof.
  unfold System.execute_DataMemoryBarrier.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_CompareAndBranch
    sf t offset iszero :
  UMPromising_Sail_no_promise
    (System.execute_CompareAndBranch sf t offset iszero).
Proof.
  unfold System.execute_CompareAndBranch.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_Branch offset :
  UMPromising_Sail_no_promise (System.execute_Branch offset).
Proof.
  unfold System.execute_Branch.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_BitwiseLogic
    sf op d n op2 :
  UMPromising_Sail_no_promise
    (System.execute_BitwiseLogic sf op d n op2).
Proof.
  unfold System.execute_BitwiseLogic.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_Add sf d n op :
  UMPromising_Sail_no_promise (System.execute_Add sf d n op).
Proof.
  unfold System.execute_Add.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Ltac destruct_unit :=
  match goal with
  | u : unit |- _ => destruct u
  end.

Ltac solve_UMPromising_Sail_no_promise_instr :=
  lazymatch goal with
  | |- UMPromising_Sail_no_promise
        (System.execute_TLBInvalidation _ _) =>
      apply UMPromising_Sail_no_promise_execute_TLBInvalidation
  | |- UMPromising_Sail_no_promise
        (System.execute_SupervisorCall _) =>
      apply UMPromising_Sail_no_promise_execute_SupervisorCall
  | |- UMPromising_Sail_no_promise (System.execute_Sub _ _ _ _) =>
      apply UMPromising_Sail_no_promise_execute_Sub
  | |- UMPromising_Sail_no_promise (System.execute_Nop ?u) =>
      destruct u; apply UMPromising_Sail_no_promise_execute_Nop
  | |- UMPromising_Sail_no_promise (System.execute_Movz _ _ _ _) =>
      apply UMPromising_Sail_no_promise_execute_Movz
  | |- UMPromising_Sail_no_promise (System.execute_Load _ _ _ _) =>
      apply UMPromising_Sail_no_promise_execute_Load
  | |- UMPromising_Sail_no_promise
        (System.execute_InstructionSynchronizationBarrier ?u) =>
      destruct u; apply UMPromising_Sail_no_promise_execute_ISB
  | |- UMPromising_Sail_no_promise
        (System.execute_ExceptionReturn ?u) =>
      destruct u;
      apply UMPromising_Sail_no_promise_execute_ExceptionReturn
  | |- UMPromising_Sail_no_promise
        (System.execute_DataSynchronizationBarrier _ _) =>
      apply UMPromising_Sail_no_promise_execute_DSB
  | |- UMPromising_Sail_no_promise
        (System.execute_DataMemoryBarrier _ _) =>
      apply UMPromising_Sail_no_promise_execute_DMB
  | |- UMPromising_Sail_no_promise
        (System.execute_CompareAndBranch _ _ _ _) =>
      apply UMPromising_Sail_no_promise_execute_CompareAndBranch
  | |- UMPromising_Sail_no_promise (System.execute_Branch _) =>
      apply UMPromising_Sail_no_promise_execute_Branch
  | |- UMPromising_Sail_no_promise
        (System.execute_BitwiseLogic _ _ _ _ _) =>
      apply UMPromising_Sail_no_promise_execute_BitwiseLogic
  | |- UMPromising_Sail_no_promise (System.execute_Add _ _ _ _) =>
      apply UMPromising_Sail_no_promise_execute_Add
  | _ => solve_UMPromising_Sail_no_promise_exec
  end.

Ltac solve_UMPromising_Sail_at_most_one_promise_instr :=
  lazymatch goal with
  | |- UMPromising_Sail_at_most_one_promise
        (System.execute_Store _ _ _ _) =>
      apply UMPromising_Sail_at_most_one_promise_execute_Store
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      first
        [eapply UMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |intro; solve_UMPromising_Sail_at_most_one_promise_instr]
        |eapply UMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_UMPromising_Sail_at_most_one_promise_instr
         |intro; solve_UMPromising_Sail_no_promise_instr]]
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Interface.iMon_bind _ _) =>
      first
        [eapply UMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |intro; solve_UMPromising_Sail_at_most_one_promise_instr]
        |eapply UMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_UMPromising_Sail_at_most_one_promise_instr
         |intro; solve_UMPromising_Sail_no_promise_instr]]
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind0 _ _) =>
      eapply UMPromising_Sail_at_most_one_promise_bind0_no_left;
      [solve_UMPromising_Sail_no_promise_instr
      |solve_UMPromising_Sail_at_most_one_promise_instr]
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.liftR _) =>
      apply UMPromising_Sail_at_most_one_promise_liftR;
      solve_UMPromising_Sail_at_most_one_promise_instr
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.catch_early_return _) =>
      apply UMPromising_Sail_at_most_one_promise_catch_early_return;
      solve_UMPromising_Sail_at_most_one_promise_instr
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_UMPromising_Sail_at_most_one_promise_instr
  | |- context[if ?x then _ else _] =>
      destruct x; solve_UMPromising_Sail_at_most_one_promise_instr
  | _ =>
      apply UMPromising_Sail_at_most_one_promise_from_no_promise;
      solve_UMPromising_Sail_no_promise_instr
  end.

Lemma UMPromising_Sail_at_most_one_promise_execute instr :
  UMPromising_Sail_at_most_one_promise (System.execute instr).
Proof.
  unfold System.execute.
  destruct instr; cbn [System.execute].
  all: repeat match goal with
  | p : _ * _ |- _ => destruct p; cbn [System.execute]
  | u : unit |- _ => destruct u; cbn [System.execute]
  end.
  all: solve_UMPromising_Sail_at_most_one_promise_instr.
Qed.

Ltac solve_UMPromising_Sail_at_most_one_promise_fetch :=
  lazymatch goal with
  | |- UMPromising_Sail_at_most_one_promise (System.execute _) =>
      apply UMPromising_Sail_at_most_one_promise_execute
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      first
        [eapply UMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |intro; solve_UMPromising_Sail_at_most_one_promise_fetch]
        |eapply UMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_UMPromising_Sail_at_most_one_promise_fetch
         |intro; solve_UMPromising_Sail_no_promise_instr]]
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Interface.iMon_bind _ _) =>
      first
        [eapply UMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |intro; solve_UMPromising_Sail_at_most_one_promise_fetch]
        |eapply UMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_UMPromising_Sail_at_most_one_promise_fetch
         |intro; solve_UMPromising_Sail_no_promise_instr]]
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind0 _ _) =>
      eapply UMPromising_Sail_at_most_one_promise_bind0_no_left;
      [solve_UMPromising_Sail_no_promise_instr
      |solve_UMPromising_Sail_at_most_one_promise_fetch]
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.liftR _) =>
      apply UMPromising_Sail_at_most_one_promise_liftR;
      solve_UMPromising_Sail_at_most_one_promise_fetch
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.catch_early_return _) =>
      apply UMPromising_Sail_at_most_one_promise_catch_early_return;
      solve_UMPromising_Sail_at_most_one_promise_fetch
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_UMPromising_Sail_at_most_one_promise_fetch
  | |- context[if ?x then _ else _] =>
      destruct x; solve_UMPromising_Sail_at_most_one_promise_fetch
  | _ => solve_UMPromising_Sail_at_most_one_promise_instr
  end.

Lemma UMPromising_Sail_at_most_one_promise_fetch_and_execute :
  UMPromising_Sail_at_most_one_promise (System.fetch_and_execute tt).
Proof.
  unfold System.fetch_and_execute.
  solve_UMPromising_Sail_at_most_one_promise_fetch.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_sail_mem_write
    tid initmem msg nondet {E n nt} req value tags :
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet
    (System_types.Defs.sail_mem_write
       (e:=E) (n:=n) (nt:=nt) req value tags).
Proof.
  cbn [System_types.Defs.sail_mem_write].
  right.
  intros [[]|abort].
  all: exact I.
Qed.

Ltac solve_UMPromising_Sail_promised_stable_read_code :=
  eapply UMPromising_Sail_promised_stable_from_no_promise_read_code;
  [eassumption|solve_UMPromising_Sail_no_promise_instr].

Ltac solve_UMPromising_Sail_prefix_promised_stable_read_code :=
  lazymatch goal with
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System_types.Interface.Ret _) =>
      exact I
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System_types.Defs.returnR _ _) =>
      exact I
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System_types.Defs.sail_mem_write _ _ _) =>
      apply UMPromising_Sail_prefix_promised_stable_sail_mem_write
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System.wMem _ _ _ _) =>
      unfold System.wMem;
      solve_UMPromising_Sail_prefix_promised_stable_read_code
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System.execute_Store _ _ _ _) =>
      unfold System.execute_Store;
      solve_UMPromising_Sail_prefix_promised_stable_read_code
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System.execute _) =>
      unfold System.execute;
      repeat match goal with
      | p : _ * _ |- _ => destruct p; cbn [System.execute]
      | u : unit |- _ => destruct u; cbn [System.execute]
      end;
      solve_UMPromising_Sail_prefix_promised_stable_read_code
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      first
        [eapply UMPromising_Sail_prefix_promised_stable_bind_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |solve_UMPromising_Sail_promised_stable_read_code
         |intro; solve_UMPromising_Sail_prefix_promised_stable_read_code]
        |eapply UMPromising_Sail_prefix_promised_stable_bind_no_right;
         [solve_UMPromising_Sail_prefix_promised_stable_read_code
         |intro; solve_UMPromising_Sail_no_promise_instr]]
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (Defs.bind _ _) =>
      unfold Defs.bind;
      first
        [eapply UMPromising_Sail_prefix_promised_stable_bind_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |solve_UMPromising_Sail_promised_stable_read_code
         |intro; solve_UMPromising_Sail_prefix_promised_stable_read_code]
        |eapply UMPromising_Sail_prefix_promised_stable_bind_no_right;
         [solve_UMPromising_Sail_prefix_promised_stable_read_code
         |intro; solve_UMPromising_Sail_no_promise_instr]]
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System_types.Interface.iMon_bind _ _) =>
      first
        [eapply UMPromising_Sail_prefix_promised_stable_bind_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |solve_UMPromising_Sail_promised_stable_read_code
         |intro; solve_UMPromising_Sail_prefix_promised_stable_read_code]
        |eapply UMPromising_Sail_prefix_promised_stable_bind_no_right;
         [solve_UMPromising_Sail_prefix_promised_stable_read_code
         |intro; solve_UMPromising_Sail_no_promise_instr]]
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System_types.Defs.bind0 _ _) =>
      eapply UMPromising_Sail_prefix_promised_stable_bind0_no_left;
      [solve_UMPromising_Sail_no_promise_instr
      |solve_UMPromising_Sail_promised_stable_read_code
      |solve_UMPromising_Sail_prefix_promised_stable_read_code]
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System_types.Defs.liftR _) =>
      first
        [eapply UMPromising_Sail_prefix_promised_stable_liftR_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |solve_UMPromising_Sail_promised_stable_read_code]
        |eapply UMPromising_Sail_prefix_promised_stable_liftR_no_right;
         solve_UMPromising_Sail_prefix_promised_stable_read_code]
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System_types.Defs.catch_early_return _) =>
      first
        [eapply
           UMPromising_Sail_prefix_promised_stable_catch_early_return_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |solve_UMPromising_Sail_promised_stable_read_code]
        |eapply
           UMPromising_Sail_prefix_promised_stable_catch_early_return_no_right;
         solve_UMPromising_Sail_prefix_promised_stable_read_code]
  | |- UMPromising_Sail_prefix_promised_stable _ _ _ _ _ =>
      progress cbn [System_types.Defs.bind Defs.bind];
      first
        [eapply UMPromising_Sail_prefix_promised_stable_bind_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |solve_UMPromising_Sail_promised_stable_read_code
         |intro; solve_UMPromising_Sail_prefix_promised_stable_read_code]
        |eapply UMPromising_Sail_prefix_promised_stable_bind_no_right;
         [solve_UMPromising_Sail_prefix_promised_stable_read_code
         |intro; solve_UMPromising_Sail_no_promise_instr]]
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_UMPromising_Sail_prefix_promised_stable_read_code
  | |- context[if ?x then _ else _] =>
      destruct x; solve_UMPromising_Sail_prefix_promised_stable_read_code
  | |- UMPromising_Sail_prefix_promised_stable _ _ _ _ _ =>
      progress cbn [System_types.Defs.bind];
      solve_UMPromising_Sail_prefix_promised_stable_read_code
  | |- UMPromising_Sail_prefix_promised_stable _ _ _ _ _ =>
      first
        [progress UMPromising_Sail_simpl;
         solve_UMPromising_Sail_prefix_promised_stable_read_code
        |apply UMPromising_Sail_prefix_promised_stable_from_no_promise;
         solve_UMPromising_Sail_no_promise_instr]
  end.

Lemma UMPromising_Sail_prefix_promised_stable_fetch_and_execute_from_read_code
    tid initmem code msg nondet :
  UMPromising_read_code_stability tid initmem code msg →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (System.fetch_and_execute tt).
Proof.
  intro Hstable.
  unfold System.fetch_and_execute.
  eapply UMPromising_Sail_prefix_promised_stable_catch_early_return_no_right.
  cbn [System_types.Defs.bind].
  eapply UMPromising_Sail_prefix_promised_stable_bind_no_left.
  - solve_UMPromising_Sail_no_promise_instr.
  - solve_UMPromising_Sail_promised_stable_read_code.
  - intro accdesc.
    cbn [System_types.Defs.bind].
    eapply UMPromising_Sail_prefix_promised_stable_bind_no_left.
    + solve_UMPromising_Sail_no_promise_instr.
    + solve_UMPromising_Sail_promised_stable_read_code.
    + intro pc.
      cbn [System_types.Defs.bind].
      eapply UMPromising_Sail_prefix_promised_stable_bind_no_left.
      * solve_UMPromising_Sail_no_promise_instr.
      * solve_UMPromising_Sail_promised_stable_read_code.
      * intro addr_opt.
        cbn [System_types.Defs.bind].
        eapply UMPromising_Sail_prefix_promised_stable_bind_no_left.
        -- destruct addr_opt; solve_UMPromising_Sail_no_promise_instr.
        -- destruct addr_opt; solve_UMPromising_Sail_promised_stable_read_code.
        -- intro addr_ret.
           cbn [System_types.Defs.bind].
           eapply UMPromising_Sail_prefix_promised_stable_bind_no_left.
           ++ solve_UMPromising_Sail_no_promise_instr.
           ++ solve_UMPromising_Sail_promised_stable_read_code.
           ++ intro machineCode.
              cbn [System_types.Defs.bind].
              eapply UMPromising_Sail_prefix_promised_stable_bind_no_left.
              ** solve_UMPromising_Sail_no_promise_instr.
              ** solve_UMPromising_Sail_promised_stable_read_code.
              ** intro instr_opt.
                 destruct instr_opt as [instr|].
                 { eapply
                     UMPromising_Sail_prefix_promised_stable_liftR_no_right.
                   unfold System.execute;
                   destruct instr; cbn [System.execute];
                   repeat match goal with
                   | p : _ * _ |- _ => destruct p; cbn [System.execute]
                   | u : unit |- _ => destruct u; cbn [System.execute]
                   end;
                   try (apply
                     UMPromising_Sail_prefix_promised_stable_from_no_promise;
                     solve_UMPromising_Sail_no_promise_instr);
                   solve_UMPromising_Sail_prefix_promised_stable_read_code. }
                 { apply
                     UMPromising_Sail_prefix_promised_stable_from_no_promise.
                   solve_UMPromising_Sail_no_promise_instr. }
Qed.

Ltac solve_UMPromising_no_promise_outcome :=
  eapply UMPromising_handle_outcome_no_promise_non_mem_write;
  intros ? ? ? Hneq; discriminate Hneq.

Ltac solve_UMPromising_cmon_no_promise :=
  repeat progress (
    cbn [Sail_outcome_interp Sail_choose Sail_nochoose
         mcall_noret mdiscard mchoosef mchoosel mchoose] in *;
    unfold mret, mbind, fmap, mthrow, mcall, mcallM,
      mcall_repl, MCall_SubEff, sub_eff, SubEff_suml, SubEff_sumr,
      iMon_throw, fMon_ret, fMon_bind, fMon_fmap, fMon_call in *;
    cbn in *);
  repeat match goal with
  | H : Empty_set |- _ => destruct H
  | H : False |- _ => contradiction
  | |- context[if ?b then _ else _] => destruct b; cbn in *
  | |- CPState.cmon_no_promise _ _ _ _ _ => progress cbn
  | |- True => exact I
  | |- _ ∧ _ => split
  | |- ∀ _, _ => intro
  | |- CPState.handle_outcome_no_promise UMPromising _ _ _ =>
      solve_UMPromising_no_promise_outcome
  end.

Ltac solve_UMPromising_cmon_at_most_one :=
  repeat progress (
    cbn [Sail_outcome_interp Sail_choose Sail_nochoose
         mcall_noret mdiscard mchoosef mchoosel mchoose] in *;
    unfold mret, mbind, fmap, mthrow, mcall, mcallM,
      mcall_repl, MCall_SubEff, sub_eff, SubEff_suml, SubEff_sumr,
      iMon_throw, fMon_ret, fMon_bind, fMon_fmap, fMon_call in *;
    cbn in *);
  repeat match goal with
  | H : Empty_set |- _ => destruct H
  | H : False |- _ => contradiction
  | |- context[if ?b then _ else _] => destruct b; cbn in *
  | |- CPState.cmon_no_promise _ _ _ _ _ => progress cbn
  | |- CPState.cmon_at_most_one_promise _ _ _ _ _ => progress cbn
  | |- True => exact I
  | |- _ ∧ _ => split
  | |- ∀ _, _ => intro
  | |- CPState.handle_outcome_no_promise UMPromising _ _ _ =>
      solve_UMPromising_no_promise_outcome
  | |- _ ∨ _ =>
      first [left; split; [solve_UMPromising_no_promise_outcome|]
            | right; solve_UMPromising_cmon_no_promise]
  end.

Ltac solve_UMPromising_cmon_at_most_one_prefix :=
  repeat progress (
    cbn [Sail_outcome_interp Sail_choose Sail_nochoose
         mcall_noret mdiscard mchoosef mchoosel mchoose] in *;
    unfold mret, mbind, fmap, mthrow, mcall, mcallM,
      mcall_repl, MCall_SubEff, sub_eff, SubEff_suml, SubEff_sumr,
      iMon_throw, fMon_ret, fMon_bind, fMon_fmap, fMon_call in *;
    cbn in *);
  repeat match goal with
  | H : Empty_set |- _ => destruct H
  | H : False |- _ => contradiction
  | |- context[if ?b then _ else _] => destruct b; cbn in *
  | |- CPState.cmon_no_promise _ _ _ _ _ => progress cbn
  | |- CPState.cmon_at_most_one_promise_prefix_stable _ _ _ _ _ _ =>
      progress cbn
  | |- True => exact I
  | |- _ ∧ _ => split
  | |- ∀ _, _ => intro
  | |- _ ∨ _ => right; solve_UMPromising_cmon_no_promise
  end.

Lemma UMPromising_Sail_outcome_no_promise_interp {n eo A}
    (tid : fin n) initmem nondet (out : SI.outcome eo A) :
  UMPromising_Sail_outcome_no_promise out →
  CPState.cmon_no_promise UMPromising tid initmem A
    (Sail_outcome_interp nondet out).
Proof.
  destruct out; intro Hout; try contradiction;
    solve_UMPromising_cmon_no_promise.
  all: destruct ty; solve_UMPromising_cmon_no_promise.
Qed.

Lemma UMPromising_Sail_outcome_at_most_one_promise_interp {n eo A}
    (tid : fin n) initmem nondet (out : SI.outcome eo A) :
  CPState.cmon_at_most_one_promise UMPromising tid initmem A
    (Sail_outcome_interp nondet out).
Proof.
  destruct out; solve_UMPromising_cmon_at_most_one.
  all: destruct ty; solve_UMPromising_cmon_at_most_one.
Qed.

Lemma UMPromising_Sail_outcome_at_most_one_prefix_stable_interp
    {n eo A} (tid : fin n) initmem msg nondet
    (out : SI.outcome eo A) :
  CPState.cmon_at_most_one_promise_prefix_stable
    UMPromising tid initmem msg A
    (Sail_outcome_interp nondet out).
Proof.
  destruct out; solve_UMPromising_cmon_at_most_one_prefix.
  all: destruct ty; solve_UMPromising_cmon_at_most_one_prefix.
Qed.

Lemma UMPromising_iMon_from_Sail_no_promise {n eo A}
    (tid : fin n) initmem nondet (smon : SI.iMon eo A) :
  UMPromising_Sail_no_promise smon →
  CPState.cmon_no_promise UMPromising tid initmem A
    (iMon_from_Sail nondet smon).
Proof.
  induction smon as [a|T out k IH]; intro Hno_promise.
  - exact I.
  - cbn in Hno_promise |- *.
    destruct Hno_promise as [Hout Htail].
    eapply CPState.cmon_no_promise_bind.
    + apply UMPromising_Sail_outcome_no_promise_interp.
      exact Hout.
    + intro ret.
      apply IH.
      apply Htail.
Qed.

Lemma UMPromising_iMon_from_Sail_at_most_one_promise {n eo A}
    (tid : fin n) initmem nondet (smon : SI.iMon eo A) :
  UMPromising_Sail_at_most_one_promise smon →
  CPState.cmon_at_most_one_promise UMPromising tid initmem A
    (iMon_from_Sail nondet smon).
Proof.
  induction smon as [a|T out k IH]; intro Hat_most.
  - exact I.
  - cbn in Hat_most |- *.
    destruct Hat_most as [[Hout Htail_at_most]|Htail_no_promise].
    + eapply CPState.cmon_at_most_one_promise_bind_no_left.
      * apply UMPromising_Sail_outcome_no_promise_interp.
        exact Hout.
      * intro ret.
        apply IH.
        apply Htail_at_most.
    + eapply CPState.cmon_at_most_one_promise_bind_no_right.
      * apply UMPromising_Sail_outcome_at_most_one_promise_interp.
      * intro ret.
        apply UMPromising_iMon_from_Sail_no_promise.
        apply Htail_no_promise.
Qed.

Lemma UMPromising_iMon_from_Sail_prefix_promised_stable
    {n eo A} (tid : fin n) initmem msg nondet
    (smon : SI.iMon eo A) :
  UMPromising_Sail_prefix_promised_stable
    (tid : nat) initmem msg nondet smon →
  CPState.cmon_at_most_one_promise_prefix_stable
    UMPromising tid initmem msg A (iMon_from_Sail nondet smon).
Proof.
  induction smon as [a|T out k IH]; intro Hstable.
  - exact I.
  - cbn in Hstable |- *.
    destruct Hstable as
      [[Hout_no [Hout_stable Htail_stable]]|Htail_no_promise].
    + eapply CPState.cmon_at_most_one_promise_prefix_stable_bind_no_left.
      * apply UMPromising_Sail_outcome_no_promise_interp.
        exact Hout_no.
      * apply UMPromising_imon_future_promise_stable_promised_to_cmon.
        exact Hout_stable.
      * intro ret.
        apply IH.
        apply Htail_stable.
    + eapply CPState.cmon_at_most_one_promise_prefix_stable_bind_no_right.
      * apply UMPromising_Sail_outcome_at_most_one_prefix_stable_interp.
      * intro ret.
        apply UMPromising_iMon_from_Sail_no_promise.
        apply Htail_no_promise.
Qed.
