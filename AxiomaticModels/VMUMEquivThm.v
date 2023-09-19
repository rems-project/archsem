Require Import Strings.String.

From stdpp Require Import decidable.

Require Import SSCCommon.Common.
Require Import SSCCommon.GRel.
Require Import SSCCommon.FMon.
Require Import ISASem.ArmInst.
Require Import ISASem.SailArmInstTypes.
Require Import GenModels.TermModels.
Module ArmTM := TermModels Arm.
Require Import GenModels.CandidateExecutions.
Module ArmCand := CandidateExecutions Arm ArmTM.
Require Import GenAxiomaticArm.

Import Arm.
Import ArmTM.
Import ArmCand.

Module Thm2.

  Import Candidate.

  (* Given the initial memory [: memoryMap], the root [: pa] of the page table,
     the range of the page table [: gset pa], this predicate checks that the
     content of the page table agrees with a characterisation function [: va -> pa] *)
  (* NOTE: this function is axiomatised for now, since it is not the main goal
     of this exercise *)
  Axiom page_table_agree_with_translate : memoryMap -> pa -> gset pa ->
                                          (va -> pa) -> Prop.

  (* This predicate is an substitution of the translate function in the paper proof *)
  Axiom translate_read_chain_agree_with_translate : ∀ nmth, Candidate.t nmth -> (va -> pa) -> Prop.

  (* A candidate generated from a full ISA *)
  Definition cd := GenAxiomaticArm.GenArm.cd.
  (* the initial memory *)
  Definition init_mem := GenAxiomaticArm.GenArm.init_mem.
  (* The candidate is wellformed *)
  Context (Hwf : GenArm.wellformed cd).
  (* this is the mathematical characterisation of the page table *)
  Context (translate : va -> pa).
  Context (translate_is_inj : FinFun.Injective translate).
  (* the address space of page table in the initial memory *)
  Context (page_table_init_address_space : gset (pa)).
  (* the page table root *)
  Context (page_table_root : pa).
  (* the address space of the program *)
  Context (vm_address_space : gset va).

  (** Hypotheses of the theorems *)
  (* the two address spaces don't overlap in physical memory *)
  Context (page_table_vm_pa_disjoint :
            set_Forall (λ va, translate va ∉ page_table_init_address_space)
              vm_address_space).

  (** Definition 1 VA abstraction subcondition *)
  (* NOTE: we do filtering on candidate instead of programs for now, later a
     similar checker for the associated program should be implemented (by
     inspecting the initial instruction memory), and a ISA lemma showing
     that if the program has no such page table affecting instructions then
     so do its candidates need to be proved. But again, that is not the goal
     of this exercise *)
  Definition no_page_table_affecting_events {n} (cd : Candidate.t n) :=
    (TLBI cd) ∪ (VMSA.ContextChange cd) = ∅.

  (* Check if the page table is static by checking the existence of page table
     write events (to the initial page table memory) in candidates. Again, we
     should have a similar check on instructions *)
  Definition is_page_table_write (event : iEvent) :=
    match event with
    | MemWrite _ wreq &→ _ =>
        wreq.(WriteReq.pa) ∈ page_table_init_address_space
    | _ => False
    end.
  Global Instance is_page_table_write_dec event
    : Decision (is_page_table_write event).
  Proof. unfold is_page_table_write. apply _. Qed.

  (* NOTE: this definition might be not very useful in the proof. We might want
   to first use another def stating that all Ts read from inital memory and later
   show this def implies that *)
  Definition page_table_is_static {n} (cd : Candidate.t n) :=
    collect_all (λ _ event, is_page_table_write event) cd = ∅.

  (** Definition 2 VA abstraction condition *)
  Definition page_table_is_injective_static {n} (cd : Candidate.t n) :=
    (* subcondition *)
    no_page_table_affecting_events cd ∧
    (* translation function is [translate] which is injective *)
    page_table_agree_with_translate init_mem page_table_root
      page_table_init_address_space translate ∧
    (* and is static *)
    page_table_is_static cd.

  (* NOTE: The erase function is identity for now since
    (a) the user model currently is defined by ignoring events - we only show
    that a full candidate with translation events etc. ignored is consistent with
    the user model, as the first step;
    (b) we don't prove properties related to ISAs, esp. after erasure the candidate
    is a candidate generated with a simplified ISA (without translation), since
    the ISAs are not ready yet.*)
  Definition erased_cd := cd.

  Definition thm2_statement :=
    VMSA.consistent cd ->
    (* NOTE: Because of the reasons of erasure being identity, we don't need any
       assumptions on the page table to prove this direction *)
    (* page_table_is_injective_static -> *)
    UM.consistent erased_cd.

  (* TODO: we also need to show VMSA.wf cd -> UM.wf cd *)

  (* TODO: move to GRel.v *)
  Lemma grel_plus_subseteq `{Countable K} (r1 r2 : grel K):
    r1 ⊆ r2 -> r1⁺ ⊆ r2⁺.
  Proof.
    intros Hsub [? ?] Hin.
    cinduction Hin.
    - apply Hsub in H0. apply grel_plus_once. assumption.
    - apply Hsub in H0. eapply grel_plus_trans.
      + apply grel_plus_once. eassumption.
      + assumption.
  Qed.

  (* XXX: the original proof starts by assuming that [addr] in VMSA coincides
     with [addr] in UM, which is not stated explicitly anywhere in this Coq
     formalisation. Since here we simply share [addr] between two models, which
     might not be strictly correct for VMSA?? *)
  Lemma thm2_proof : thm2_statement.
  Proof.
    intros Hvm_cs. destruct Hvm_cs.
    assert (UM.po erased_cd ⊆ VMSA.po cd) as Hpo.
    {
      unfold UM.po, VMSA.po. clear.
      Local Typeclasses Opaque W R F C loc instruction_order.
      set_unfold. hauto lq:on.
      Local Typeclasses Transparent W R F C loc instruction_order.
    }
    Local Typeclasses Opaque UM.po VMSA.po.
    split.
    - assert (UM.po_loc erased_cd ⊆ VMSA.po_loc cd).
      {
        unfold UM.po_loc, VMSA.po_loc.
        clear - Hpo.
        set_solver + Hpo.
      }
      Local Typeclasses Opaque UM.po_loc VMSA.po_loc.
      assert (UM.fr erased_cd = VMSA.fr cd) as ->.
      {
        clear. set_unfold. done.
      }
      assert (UM.co erased_cd = VMSA.co cd) as ->.
      {
        clear. set_unfold. done.
      }
      assert (UM.rf erased_cd = VMSA.rf cd) as ->.
      {
        clear. set_unfold. done.
      }
      clear - internal H.
      Local Typeclasses Opaque VMSA.rf VMSA.fr VMSA.co.
      assert (UM.po_loc erased_cd ∪ VMSA.fr cd ∪ VMSA.co cd ∪ VMSA.rf cd
        ⊆ VMSA.po_loc cd ∪ VMSA.fr cd ∪ VMSA.co cd ∪ VMSA.rf cd).
      set_solver + H.
      clear H. apply grel_plus_subseteq in H0.
      set_solver.
      Local Typeclasses Transparent VMSA.rf VMSA.fr VMSA.co.
    - assert (UM.ob erased_cd ⊆ VMSA.ob cd) as Hincl.
      {
        clear internal atomic translation_internal.
        unfold UM.ob, VMSA.ob. apply grel_plus_subseteq.
        unfold UM.ob1, VMSA.ob1.
        assert (UM.obs erased_cd ⊆ VMSA.obs cd) as Hobs.
        {
          unfold UM.obs, VMSA.obs.
          assert (UM.co erased_cd ⊆ VMSA.wco cd).
          {
            set_unfold; hauto.
          }
          clear external. set_unfold; sauto lq:on.
        }
        assert (UM.dob erased_cd ⊆ VMSA.dob cd ∪ VMSA.ctxob cd) as Hdob.
        {
          unfold UM.dob, VMSA.dob.
          assert (ctrl erased_cd ⨾ ⦗W erased_cd⦘ ⊆ VMSA.speculative cd ⨾ ⦗W cd⦘)
            as Hdob.
          {
            unfold VMSA.speculative. clear Hobs external.
            set_unfold. hauto lq: on rew: off.
          }
          clear -Hdob Hpo.
          assert ((ctrl erased_cd ∪ addr erased_cd ⨾ UM.po erased_cd) ⨾ ⦗isb erased_cd⦘
                    ∪ ⦗isb erased_cd⦘ ⨾ UM.po erased_cd ⨾ ⦗R erased_cd⦘ ⊆ VMSA.ctxob cd) as Hctxob.
          {
            unfold VMSA.ctxob.
            apply union_subseteq. split.
            - clear - Hpo.
              assert (ctrl erased_cd ∪ (addr erased_cd ⨾ UM.po erased_cd)
                        ⊆  VMSA.speculative cd).
              {
                unfold VMSA.speculative.
                hauto lq:on simp+:set_unfold.
              }
              unfold VMSA.CSE. set_unfold. hauto lq:on.
            - transitivity (⦗VMSA.CSE cd⦘ ⨾ instruction_order cd).
              + assert ( UM.po erased_cd ⨾ ⦗R erased_cd⦘ ⊆ instruction_order cd).
                {
                  clear - Hpo.
                  unfold UM.po. set_solver.
                }
                clear -H.
                Local Typeclasses Opaque isb UM.po R instruction_order.
                unfold VMSA.CSE. set_solver.
                Local Typeclasses Transparent isb UM.po R instruction_order.
              + Local Typeclasses Opaque VMSA.CSE instruction_order VMSA.speculative MSR VMSA.ContextChange.
                set_solver.
                Local Typeclasses Transparent VMSA.CSE instruction_order VMSA.speculative MSR VMSA.ContextChange.
          }
          Local Typeclasses Opaque VMSA.CSE VMSA.speculative VMSA.ctxob W R isb UM.po VMSA.trfi VMSA.po.
          set_unfold. hauto lq: on rew: off.
          Local Typeclasses Transparent VMSA.CSE VMSA.speculative VMSA.ctxob W R isb UM.po VMSA.trfi VMSA.po.
        }
        assert (UM.aob erased_cd ⊆ VMSA.aob cd) as Haob.
        {
          set_solver +.
        }
        assert (UM.bob erased_cd ⊆ VMSA.bob cd) as Hbob.
        {
          unfold UM.bob, VMSA.bob.
          clear - Hpo.
          Local Typeclasses Opaque  W R L A Q dmbld dmbst dmbsy dsb dsbsy isb UM.po VMSA.po.
          set_unfold. hauto lq: on rew: off.
          Local Typeclasses Transparent W R L A Q dmbld dmbst dmbsy dsb dsbsy isb UM.po VMSA.po.
        }
        clear external.
        (* make definitions opaque to avoid unnecessary unfolding *)
        Local Typeclasses Opaque UM.obs VMSA.obs UM.dob VMSA.dob UM.aob VMSA.aob
          UM.bob VMSA.bob VMSA.tob VMSA.obtlbi VMSA.ctxob VMSA.obfault VMSA.obETS.
        set_unfold. sauto lq:on.
      }
      set_solver + Hincl external.
    - assumption.
  Admitted.

  (* Definition 4 translation extension *)
  (* NOTE: we omit this step for now, just assuming that the VMSA candidate cd
     is obtained after the extension, then we write down the charactorisations of
     the extension (correspond to the 5 extension items) as some assumptions below.
   *)
  Definition translation_extension_cd := cd.

  (* Point 1: Instead of adding initial writes, we assume all page table writes
     are initial writes, namely no page table writes except for initial writes,
     or page table is static *)
  Definition translation_extension_initial_writes {n} (cd : Candidate.t n) :=
    page_table_is_static cd.

  (* Immediate iio *)
  Definition iio_imm {n} (cd : Candidate.t n) := iio cd ∖ (iio cd ⨾ iio cd).

  (* Point 2,3, and 5: Instead of adding translation reads, we assume all translate
     reads read from initial page table writes (which is derivable from WF), whose
     charactorisation is the translate function; and instead of inserting translate
     reads, we assume each memory access is immediately iio ordered-before the
     chain of proper translate reads *)
  (* NOTE the translate function is not the one in the paper proof *)
  Record translation_extension_translate_reads {n} (cd : Candidate.t n) := {
      (* the trf is empty, this means Ts only read from initial writes (given WF) *)
      trf_empty: grel_rng (VMSA.trf cd) = ∅;
      (* all Ts read from page table address space *)
      T_rf_init: collect_all
                   (λ _ event, is_translate event
                               ∧ match get_pa event with
                                 | Some pa => pa ∈ page_table_init_address_space
                                 | _ => False
                                 end) cd
                 = T cd;
      (* page table's charactorisation is translate *)
      page_table_is_translate : page_table_agree_with_translate init_mem
                                  page_table_root
                                  page_table_init_address_space translate;
      (* no translate reads that cause translation fault *)
      no_T_f : T_f cd = ∅ ;
      (* this is a quite strong assumption, but should be fine for this exercise *)
      no_MSR : MSR cd = ∅ ;
      (* all Ts that are supposed to be added to the user candidate by translation
       extensions are in a chain of form [T];same_translation;[T];...imm(iio);[M] *)
      T_in_chain :
      T cd = grel_dom(⦗T cd⦘
                         ⨾(((VMSA.same_translation cd)∩ iio_imm cd)⨾⦗T cd⦘)⁺
                         ⨾iio_imm cd⨾⦗W cd ∪ R cd⦘);
      (* TODO: more conditions TBA, unclear for now *)
      T_correct_in_cd : translate_read_chain_agree_with_translate n cd translate
    }.

  (* NOTE: Point 4 needs no charactorisation, since we assume addr coincides *)

  (* Definition 5: VA anti anstraction condition *)
  (* NOTE: just a conjunction *)
  Definition translation_events_and_relations_are_simple_and_nice {n} (cd : Candidate.t n) :=
    translation_extension_initial_writes cd
    ∧ translation_extension_translate_reads cd
    ∧ no_page_table_affecting_events cd
    ∧ UM.consistent cd.

  (* Lemma 1 VA abstraction condition for translation extension *)
  (* NOTE: we are cheating here since we don't have extension. So we simply check
     if we are missing any conditions *)
  Definition conditions_sanity_check :
    translation_events_and_relations_are_simple_and_nice translation_extension_cd ->
    page_table_is_injective_static translation_extension_cd.
  Proof.
    intros (?&?&?&?). destruct H0.
    split; first assumption.
    split; assumption.
  Qed.

  Section obtlbi_empty.

  Lemma obtlbi_empty n (cd : Candidate.t n) :
    translation_events_and_relations_are_simple_and_nice cd ->
    VMSA.obtlbi cd = ∅.
  Proof.
    intros (?&?&?&?).
    clear - H1.
    unfold VMSA.obtlbi.
    assert (VMSA.obtlbi_translate cd = ∅).
    {
      unfold VMSA.obtlbi_translate.
      Local Typeclasses Opaque T VMSA.Stage1 VMSA.tlb_barriered
      VMSA.maybe_TLB_cached VMSA.trf VMSA.same_translation.
      assert (TLBI cd = ∅). set_unfold; sauto lq:on. clear H1.
      assert (VMSA.TLBI_S1 cd = ∅).
      {
        Local Typeclasses Opaque VMSA.is_tlbi_op.
        set_unfold.
        (* FIXME: hauto & sauto are very slow *)
        unfold is_tlbi in H.
        intros ? [? [? ?]]. apply (H x).
        eexists. split; first eassumption.
        unfold VMSA.has_tlbi_op. unfold VMSA.has_tlb_op_P. hauto.
      }
      assert (VMSA.TLBI_S2 cd = ∅).
      {
        set_unfold.
        unfold is_tlbi in H.
        intros ? [? [? ?]]. apply (H x).
        eexists. split; first eassumption.
        unfold VMSA.has_tlbi_op. unfold VMSA.has_tlb_op_P. hauto.
      }
        Local Typeclasses Opaque VMSA.TLBI_S1 VMSA.TLBI_S2.
      set_unfold. hauto lq: on.
    }
    assert (⦗R cd ∪ W cd ∪ VMSA.Fault cd⦘ ⨾ (iio cd) ⁻¹
              ⨾ VMSA.obtlbi_translate cd ∖ int cd ⨾ ⦗TLBI cd⦘ = ∅).
    {
      Local Typeclasses Opaque VMSA.Fault VMSA.obtlbi_translate R W int.
      set_unfold. sauto lq:on.
    }
    set_unfold. hauto lq:on.
  Qed.
  End obtlbi_empty.

  Section po_pa_W_trf_empty.

    (* Lemma 3 the proof is easier than paper version, due to our treatment of
     initial writes *)
  Lemma po_pa_W_trf_empty {n} (cd : Candidate.t n) :
    GenArm.wellformed cd ->
    translation_events_and_relations_are_simple_and_nice cd ->
    grel_acyclic (VMSA.po_pa cd ∪ VMSA.trfi cd).
  Proof.
    intros Hwf (?&?&?&?). destruct H0.
    clear -trf_empty0 Hwf.
    assert (VMSA.trfi cd = ∅) as ->.
    {
      clear - trf_empty0.
      Local Typeclasses Opaque VMSA.trf.
      unfold VMSA.trfi.
      set_unfold. hauto.
    }
    clear trf_empty0. unfold VMSA.po_pa.
    destruct Hwf. destruct generic_po0.
    apply grel_transitive_rew in generic_po_trans.
    clear -generic_po_irr generic_po_trans.
    set_unfold.
    intros ? Hin.
    assert ((instruction_order cd ∪ iio cd) ∩ loc cd ⊆ generic_po cd) as Hsub.
    {
      clear. unfold iio, instruction_order.
      set_unfold. sauto.
    }
    apply grel_plus_subseteq in Hsub.
    rewrite union_empty_r_L in Hin.
    apply Hsub in Hin. rewrite generic_po_trans in Hin.
    eapply generic_po_irr. eassumption.
  Qed.

  End po_pa_W_trf_empty.

  Section ob_to_T.
    (* TODO: it is unclear how to state it properly at this moment, so skip *)
    Lemma ob_to_T {n} (cd : Candidate.t n):
      translation_events_and_relations_are_simple_and_nice cd ->
      VMSA.ob cd ⨾⦗T cd⦘
      = iio cd.
    Proof. Admitted.
  End ob_to_T.

  Section no_cycle_ob_to_init.
    (* Lemma 5 *)
    (* NOTE: we don't really need this lemma, neither can state it because of
     our treatment of initial writes *)
    Lemma no_cycle_ob_to_init : True.
    Proof. done. Qed.
  End no_cycle_ob_to_init.

  (* TODO: move to GRel.v *)
  (* things about grel_seq *)
  Lemma grel_seq_union_r `{Countable K} (r1 r2 r2' : grel K):
    r1 ⨾ (r2 ∪ r2') = (r1 ⨾ r2) ∪ (r1 ⨾ r2').
  Proof.
    set_unfold. hauto lq:on.
  Qed.

  Lemma grel_seq_union_l `{Countable K} (r1 r1' r2 : grel K):
    (r1 ∪ r1') ⨾ r2 = (r1 ⨾ r2) ∪ (r1' ⨾ r2).
  Proof.
    set_unfold. hauto lq:on.
  Qed.

  Global Instance grel_seq_assoc `{Countable K}: Assoc (=) ( (@grel_seq K _ _) ).
  Proof.
    intros ??. set_unfold. hauto lq:on.
  Qed.

  Section ob_from_T.

    Definition M {n} (cd : Candidate.t n) :=
      collect_all (λ _ event, is_mem_event event) cd.

    (* NOTE: the paper version of this lemma is wrong:
       it doesn't have the last case ([T];instruction-order;[ISB]) on the RHS *)
    Lemma ob_from_T {n} (cd : Candidate.t n) :
      translation_events_and_relations_are_simple_and_nice cd ->
      GenArm.wellformed cd ->
      (* We simply assume the extended candidate is wf wrt VMSA, but this is a
       property about the extension that we want to show *)
      VMSA.wf cd init_mem ->
      ⦗T cd⦘⨾VMSA.ob1 cd =
      iio cd
        ∪ (⦗T cd⦘⨾iio cd ⨾⦗M cd⦘⨾ VMSA.po cd ⨾⦗W cd⦘)
        ∪ (⦗T cd⦘⨾ instruction_order cd ⨾ ⦗isb cd⦘).
    Proof.
      intros (?&?&?&?) Hwf Hvmsa_wf. unfold VMSA.ob1.
      (* general proof strategy: check all clauses of ob1 *)
      unfold VMSA.obs.
      assert (T cd ## W cd) as H_T_W_disj.
      {
        (* FIXME: seemed hauto is not smart enough for things like it *)
        clear. set_unfold. unfold is_translate, is_mem_write.
        intros ? (?&Hlk1&?) (?&Hlk2&?).
        rewrite Hlk1 in Hlk2.
        hauto lq: on rew: off.
      }
      assert (T cd ## C cd) as H_T_C_disj.
      {
        clear. set_unfold. unfold is_translate, is_mem_read.
        intros ? (?&Hlk1&?) (?&Hlk2&?).
        rewrite Hlk1 in Hlk2.
        hauto lq: on rew: off.
      }
      assert (T cd ## R cd) as H_T_R_disj.
      {
        clear. set_unfold. unfold is_translate, is_mem_read.
        intros ? (?&Hlk1&?) (?&Hlk2&?).
        unfold is_explicit_access_kind_P in H0.
        rewrite Hlk1 in Hlk2; inversion Hlk2; subst.
        destruct x1 as [T call ret]. destruct call;try assumption. rewrite H in H0.
        hauto lq:on.
      }
      assert (⦗T cd⦘⨾ (VMSA.rfe cd) = ∅).
      {
        unfold VMSA.rfe. unfold VMSA.rf. clear - H_T_W_disj.
        Local Typeclasses Opaque VMSA.rfi R T W.
        set_unfold. sauto lq:on.
        Local Typeclasses Transparent VMSA.rfi R T W.
      }
      assert (⦗T cd⦘⨾ (VMSA.fr cd) = ∅).
      {
        unfold VMSA.fr. clear - H_T_W_disj.
        Local Typeclasses Opaque VMSA.co VMSA.rf T W.
        set_unfold. sauto lq:on.
        Local Typeclasses Transparent VMSA.co VMSA.rf R T W.
      }
      assert (⦗T cd⦘⨾ (VMSA.wco cd) = ∅).
      {
        destruct Hvmsa_wf. clear - wco_wf H_T_C_disj H_T_W_disj.
        destruct wco_wf. clear -H_T_C_disj H_T_W_disj wco_dom.
        set_unfold. ecrush lq: on.
      }
      assert (⦗T cd⦘⨾ (VMSA.trfe cd) = ∅).
      {
        unfold VMSA.trfe. destruct H0. clear -trf_empty0.
        Local Typeclasses Opaque VMSA.trfi T.
        set_unfold. sauto lq:on.
        Local Typeclasses Transparent VMSA.trfi T.
      }
      assert (⦗T cd⦘⨾ (VMSA.dob cd)
              = ⦗T cd⦘ ⨾ instruction_order cd ⨾ ⦗W cd⦘).
      {
        unfold VMSA.dob.
        assert (⦗T cd⦘⨾ (addr cd) = ∅).
        {
          destruct Hwf. destruct addr0. clear - addr_dom H_T_R_disj.
          Local Typeclasses Opaque T R.
          set_unfold. sauto lq: on rew: off.
          Local Typeclasses Transparent T R.
        }
        assert (⦗T cd⦘⨾ (data cd) = ∅).
        {
          destruct Hwf. destruct data0. clear - data_dom H_T_R_disj.
          Local Typeclasses Opaque T R.
          set_unfold. sauto lq: on rew: off.
          Local Typeclasses Transparent T R.
        }
        assert (⦗T cd⦘⨾ (ctrl cd) = ∅).
        {
          destruct Hwf. destruct ctrl0. clear - ctrl_dom H_T_R_disj.
          Local Typeclasses Opaque T R.
          set_unfold. sauto lq: on rew: off.
          Local Typeclasses Transparent T R.
        }
        assert (⦗T cd⦘ ⨾ addr cd ⨾ VMSA.po cd = ∅ ).
        {
          Local Typeclasses Opaque VMSA.po addr T.
          clear -H7.
          set_unfold.
          intros ? (?&?&?). apply (H7 (x.1, x0)). simpl. assumption.
          Local Typeclasses Transparent VMSA.po addr T.
        }
        assert (⦗T cd⦘⨾ (addr cd ⨾ VMSA.po cd ⨾ ⦗W cd⦘) = ∅).
        {
          clear -H10.
          rewrite assoc. 2: apply _.
          Local Typeclasses Opaque T addr VMSA.po.
          set_unfold. sauto lq: on rew: off.
          Local Typeclasses Transparent T addr VMSA.po.
        }
        assert (⦗T cd⦘⨾ (VMSA.speculative cd ⨾ ⦗W cd⦘)
                = ⦗T cd⦘ ⨾ instruction_order cd ⨾⦗W cd⦘).
        (* TODO: We further need to use [T_in_chain] to show that there must be a
         iio ordered after [M] before [W] *)
        {
          unfold VMSA.speculative.
          Local Typeclasses Opaque T W instruction_order ctrl data addr VMSA.po.
          clear - H10 H9.
          rewrite assoc. 2: apply _.
          assert (⦗T cd⦘ ⨾ (ctrl cd ∪ addr cd ⨾ VMSA.po cd) = ∅ ).
          {
            set_unfold. hauto lq:on.
          }
          clear H9.
          set_unfold. hauto lq: on.
          Local Typeclasses Transparent T W instruction_order ctrl data addr VMSA.po.
        }
        assert (⦗T cd⦘⨾ ((addr cd ∪ data cd) ⨾ VMSA.rfi cd) = ∅).
        {
          clear - H7 H8.
          Local Typeclasses Opaque T W instruction_order data addr VMSA.po VMSA.rfi.
          rewrite assoc. 2: apply _.
          set_unfold.
          intros ? (?&?&?). destruct H as (? & ?& [? |?]).
          apply (H7 (x1, x0)). hauto l:on.
          apply (H8 (x1, x0)). hauto l:on.
          Local Typeclasses Transparent T W instruction_order data addr VMSA.po VMSA.rfi.
        }
        assert (⦗T cd⦘⨾ ((addr cd ∪ data cd) ⨾ VMSA.trfi cd) = ∅).
        {
          clear - H7 H8.
          Local Typeclasses Opaque T W instruction_order data addr VMSA.po VMSA.rfi.
          rewrite assoc. 2: apply _.
          set_unfold.
          intros ? (?&?&?). destruct H as (? & ?& [? |?]).
          apply (H7 (x1, x0)). hauto l:on.
          apply (H8 (x1, x0)). hauto l:on.
          Local Typeclasses Transparent T W instruction_order data addr VMSA.po VMSA.rfi.
        }
        clear -H7 H8 H9 H11 H12 H13 H14.
        Local Typeclasses Opaque T W data addr ctrl VMSA.speculative VMSA.rfi VMSA.trfi instruction_order VMSA.po.
        repeat rewrite grel_seq_union_r.
        rewrite H7, H8, H11, H12, H13, H14.
        clear.
        set_unfold. hauto lq:on.
        Local Typeclasses Transparent T W data addr ctrl VMSA.speculative VMSA.rfi VMSA.trfi instruction_order VMSA.po.
      }
      assert (⦗T cd⦘⨾ (VMSA.aob cd) = ∅).
      {
        unfold VMSA.aob.
        (* FIXME need WF lxsx amo, easy *)
        admit.
      }
      assert (⦗T cd⦘⨾ (VMSA.bob cd) = ∅).
      {
        unfold VMSA.bob.
        clear - H_T_W_disj H_T_C_disj H_T_R_disj.
        assert (T cd ## L cd) as H_T_L_disj.
        {
          clear. set_unfold. unfold is_translate, is_mem_read.
          intros ? (?&Hlk1&?) (?&Hlk2&?).
          rewrite Hlk1 in Hlk2.
          hauto rew:off lq:on.
        }
        assert (T cd ## Q cd) as H_T_Q_disj.
        {
          clear. set_unfold. unfold is_translate, is_mem_read.
          intros ? (?&Hlk1&?) (?&Hlk2&?).
          rewrite Hlk1 in Hlk2; inversion Hlk2; subst.
          destruct x1 as [T call ret]. unfold is_explicit_access_kind_P in H0.
          destruct call;try assumption. rewrite H in H0.
          hauto lq:on.
        }
        assert (T cd ## A cd) as H_T_A_disj.
        {
          clear. set_unfold. unfold is_translate, is_mem_read.
          intros ? (?&Hlk1&?) (?&Hlk2&?).
          rewrite Hlk1 in Hlk2; inversion Hlk2; subst.
          destruct x1 as [T call ret]. unfold is_explicit_access_kind_P in H0.
          destruct call;try assumption. rewrite H in H0.
          hauto lq:on.
        }
        assert (T cd ## F cd) as H_T_F_disj.
        {
          clear. set_unfold. unfold is_translate, is_mem_read.
          intros ? (?&Hlk1&?) (?&Hlk2&?).
          rewrite Hlk1 in Hlk2.
          hauto rew:off lq:on.
        }
        assert (T cd ## dmbst cd) as H_T_dmbst_disj.
        {
          clear. set_unfold. unfold is_translate, is_mem_read.
          intros ? (?&Hlk1&?) (?&Hlk2&?).
          rewrite Hlk1 in Hlk2.
          hauto rew:off lq:on.
        }
        assert (T cd ## dmbld cd) as H_T_dmbld_disj.
        {
          clear. set_unfold. unfold is_translate, is_mem_read.
          intros ? (?&Hlk1&?) (?&Hlk2&?).
          rewrite Hlk1 in Hlk2.
          hauto rew:off lq:on.
        }
        assert (T cd ## dsb cd) as H_T_dsb_disj.
        {
          clear. set_unfold. unfold is_translate, is_mem_read.
          intros ? (?&Hlk1&?) (?&Hlk2&?).
          rewrite Hlk1 in Hlk2.
          hauto rew:off lq:on.
        }
        Local Typeclasses Opaque T R W dmbst dmbld L A Q F C dsb dsbsy.
        set_unfold. ecrush drew: off lq: on.
        Local Typeclasses Transparent T R W dmbst dmbld L A Q F C dsb dsbsy.
      }
      assert (⦗T cd⦘⨾ VMSA.tob cd = ∅).
      {
        unfold VMSA.tob.
        rewrite grel_seq_union_r.
        do 2 rewrite grel_seq_assoc.
        destruct H0.
        rewrite no_T_f0.
        assert (VMSA.trfi cd = ∅) as ->.
        {
          unfold VMSA.trfi. clear -trf_empty0.
          Local Typeclasses Opaque VMSA.trf int.
          set_unfold. hauto lq: on.
          Local Typeclasses Transparent VMSA.trf int.
        }
        clear.
        Local Typeclasses Opaque T VMSA.tfr VMSA.speculative.
        set_unfold. hauto lq: on.
        Local Typeclasses Transparent T VMSA.tfr VMSA.speculative.
      }
      assert (⦗T cd⦘⨾ VMSA.obtlbi cd = ∅).
      {
        unfold VMSA.obtlbi.
        rewrite grel_seq_union_r.
        assert (⦗T cd⦘⨾ VMSA.obtlbi_translate cd = ∅) as ->.
        {
          unfold VMSA.obtlbi_translate.
          repeat rewrite grel_seq_union_r.
          repeat rewrite grel_seq_assoc.
          assert (⦗VMSA.TLBI_S1 cd⦘ = ∅) as ->.
          {
            clear -H1.
            unfold no_page_table_affecting_events in H1.
            Local Typeclasses Opaque VMSA.ContextChange.
            set_unfold.
            unfold VMSA.has_tlbi_op. unfold VMSA.has_tlb_op_P. unfold is_tlbi in H1.
            intros ? ([e ?]&Heq). apply (H1 x.1).
            left.  destruct e as [T call ret]. destruct call; hauto lq:on.
          }
          assert (⦗VMSA.TLBI_S2 cd⦘ = ∅) as ->.
          {
            clear -H1.
            unfold no_page_table_affecting_events in H1.
            set_unfold.
            unfold VMSA.has_tlbi_op. unfold VMSA.has_tlb_op_P. unfold is_tlbi in H1.
            intros ? ([e ?]&Heq). apply (H1 x.1).
            left.  destruct e as [T call ret]. destruct call; hauto lq:on.
          }
          Local Typeclasses Opaque T VMSA.Stage1 VMSA.tlb_barriered VMSA.Stage2 VMSA.trf VMSA.wco VMSA.same_translation valid_eids VMSA.maybe_TLB_cached.
          clear.
          set_unfold. hauto lq:on.
          Local Typeclasses Transparent VMSA.ContextChange T VMSA.Stage1 VMSA.tlb_barriered VMSA.Stage2 VMSA.trf VMSA.wco VMSA.same_translation valid_eids VMSA.maybe_TLB_cached.
        }
        assert (⦗TLBI cd⦘ = ∅) as ->.
        {
        unfold no_page_table_affecting_events in H1.
        clear -H1. set_unfold. hauto lq:on.
        }
        clear.
        Local Typeclasses Opaque T R W VMSA.Fault iio VMSA.obtlbi_translate int.
        set_unfold. hauto lq: on.
        Local Typeclasses Transparent T R W VMSA.Fault iio VMSA.obtlbi_translate int.
      }
      assert (⦗T cd⦘⨾ VMSA.ctxob cd =⦗T cd⦘⨾ instruction_order cd ⨾ ⦗isb cd⦘).
      {
        unfold VMSA.ctxob.
        do 2 rewrite grel_seq_union_r.
        rewrite grel_seq_union_r.
        assert (⦗T cd⦘⨾ (VMSA.speculative cd ⨾ ⦗VMSA.CSE cd⦘)
                = ⦗T cd⦘⨾ instruction_order cd ⨾ ⦗isb cd⦘) as -> .
        {
          rewrite grel_seq_assoc.
          (* easy *)
          admit.
        }
        assert (⦗VMSA.ContextChange cd⦘ = ∅) as ->.
        {
        unfold no_page_table_affecting_events in H1.
        clear -H1. set_unfold. hauto lq:on.
        }
        assert (⦗MSR cd⦘ = ∅) as ->.
        {
          destruct H0. rewrite no_MSR0. done.
        }
        assert (⦗T cd⦘ ⨾ (⦗VMSA.CSE cd⦘ ⨾ instruction_order cd) = ∅) as ->.
        {
          rewrite grel_seq_assoc. unfold VMSA.CSE.
          assert (T cd ## isb cd ∪ TE cd ∪ ERET cd) as H_T_disj.
          {
            clear. set_unfold. unfold is_translate, is_mem_read.
            intros ? (?&Hlk1&?) [[(?&Hlk2&?)|(?&Hlk2&?)]|(?&Hlk2&?)];
            rewrite Hlk1 in Hlk2; hauto rew:on lq:on.
          }
          clear -H_T_disj.
          Local Typeclasses Opaque T isb TE ERET.
          set_unfold. hauto lq: on.
          Local Typeclasses Transparent T isb TE ERET.
        }
        clear.
        Local Typeclasses Opaque T VMSA.speculative VMSA.po VMSA.CSE instruction_order.
        set_unfold. hauto lq: on.
        Local Typeclasses Transparent T VMSA.speculative VMSA.po VMSA.CSE instruction_order.
      }
      assert (⦗T cd⦘⨾ VMSA.obfault cd = ∅).
      {
        unfold VMSA.obfault.
        do 4 rewrite grel_seq_union_r.
        do 8 rewrite grel_seq_assoc.
        (* easy *)
        admit.
      }
      assert (⦗T cd⦘⨾ VMSA.obETS cd = ∅).
      {
        unfold VMSA.obETS.
        rewrite grel_seq_union_r.
        assert (⦗TLBI cd⦘ = ∅) as ->.
        {
        unfold no_page_table_affecting_events in H1.
        clear -H1. set_unfold. hauto lq:on.
        }
        do 3 rewrite grel_seq_assoc.
        rewrite H13.
        clear.
        Local Typeclasses Opaque T VMSA.Fault_T iio T_f VMSA.po instruction_order VMSA.tlb_affects.
        set_unfold. hauto lq: on.
        Local Typeclasses Transparent T VMSA.Fault_T iio T_f VMSA.po instruction_order VMSA.tlb_affects.
      }
    Admitted.

  End ob_from_T.

  (* TODO: incomplete *)
  Definition thm3_statement :=
    UM.consistent cd ->
    page_table_is_injective_static cd ->
    VMSA.consistent cd.

  Lemma thm3_proof : thm3_statement.
  Proof. Admitted.

End Thm2.
