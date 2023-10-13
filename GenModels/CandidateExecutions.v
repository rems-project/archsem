(** This file provide an common type for representing candidate executions
    for all memory models to use *)

(** TODO: document choices and caveats:
  - finite executions and relations
  - computable relations and allowedness
  - relation over event IDs, need to lookup candidate to get event content
 *)


Require Import Ensembles.

Require Import Strings.String.

From stdpp Require Export listset.
From stdpp Require Export gmap.

Require Import SSCCommon.Common.
Require Import SSCCommon.Exec.
Require Import SSCCommon.GRel.

Require Import ISASem.Interface.
Require Import ISASem.Deps.
Require Import TermModels.

Open Scope Z_scope.
Open Scope stdpp_scope.



(* to be imported *)
Module CandidateExecutions (IWD : InterfaceWithDeps) (Term : TermModelsT IWD).
  Import IWD.
  Import Term.
  Notation outcome := (IWD.outcome DepOn.t empOutcome).
  Notation iMon := (IWD.iMon DepOn.t empOutcome).
  Notation iSem := (IWD.iSem DepOn.t empOutcome).
  Notation iEvent := (IWD.iEvent DepOn.t empOutcome).
  Notation iTrace := (IWD.iTrace DepOn.t empOutcome).

  (* event ID *)
  Module EID.
    Record t :=
      make {
          (* thread ID *)
          tid : nat;
          (* Instruction ID *)
          iid : nat;
          (* event number *)
          num : nat
          }.

    #[global] Instance eta : Settable _ :=
        settable! make <tid; iid; num>.

    #[global] Instance eq_dec : EqDecision t.
    Proof. solve_decision. Defined.


    #[global] Instance countable : Countable t.
    Proof.
      eapply (inj_countable' (fun eid => (tid eid, iid eid, num eid))
                        (fun x => make x.1.1 x.1.2 x.2)).
      sauto.
    Qed.
  End EID.


  (* Add a hint for resolving decision instances *)
  #[export] Hint Extern 10 (Decision (match ?x with _ => _ end)) =>
    destruct x : typeclass_instances.

  Module Candidate.

    Record t :=
      make {
          num_threads : nat;
          (** Initial state *)
          init : MState.t num_threads;
          (** Each thread is a list of instruction who each have a trace,
              we force the return type to be unit, but it just means we
              forget the actual value *)
          events : vec (list (iTrace ())) num_threads;
          (* TODO po can be deduced by the order of events in the trace *)
          (** Program order. The per-thread order of all events in the trace *)
          po : grel EID.t;
          (** Memory read from *)
          rf : grel EID.t;
          (** Memory coherence: for each pa, list of writes in order *)
          co : grel EID.t;
          (** Register read from (needed because of potentially relaxed register) *)
          rrf : grel EID.t;
          (* TODO can be deduced from trace structure *)
          (** Same instruction, should be an equivalence relation. *)
          si : grel EID.t;
          (** intra-instruction address dependencies (to memory events) *)
          iio_addr : grel EID.t;
          (** intra-instruction data dependencies (to memory and register writes) *)
          iio_data : grel EID.t;
          (** intra-instruction control dependencies (to branches) *)
          iio_ctrl : grel EID.t;
        }.

    (** Asserts that a candidate conforms to an ISA model.
        This version only supports ISA model without inter-instruction state.
        We'll see later if such state is required *)
    Definition ISA_match (cd : t) (isem : iMon ()) :=
      ∀ tid : fin cd.(num_threads),
      ∀'trc ∈ cd.(events) !!! tid,
      iTrace_match isem trc.

    (** Get an event at a given event ID in a candidate *)
    Global Instance lookup_eid : Lookup EID.t iEvent t :=
      fun eid cd =>
        traces ← cd.(events) !! eid.(EID.tid);
        '(trace, result) ← traces !! eid.(EID.iid);
        trace !! eid.(EID.num).

    (** This true if one of the thread had an ISA model failure
        like a Sail assertion or an Isla assumption that failed *)
    Definition failed (cd : t) : bool :=
      existsb (fun traces =>
                 let '(trace, trace_end) := List.last traces ([], inl ()) in
                 match trace_end with | inr _ => true | inl _ => false end)
              cd.(events).

    Definition event_list (cd : t) : list (EID.t*iEvent) :=
      '(tid, traces) ← enumerate cd.(events);
      '(iid, (trace, trace_end)) ← enumerate traces;
       '(num, event) ← enumerate trace;
       [(EID.make tid iid num, event)].

    Global Typeclasses Opaque event_list.

    Import SetUnfoldPair.

    Lemma event_list_match cd eid ev :
      cd !! eid = Some ev ↔ (eid, ev) ∈ event_list cd.
    Proof.
      (* Unfold everything properly on both side, and naive_solver does it. *)
      unfold lookup at 1.
      unfold lookup_eid.
      repeat setoid_rewrite bind_Some.
      unfold event_list.
      destruct eid.
      set_unfold.
      repeat setoid_rewrite exists_pair.
      setoid_rewrite lookup_unfold.
      naive_solver.
    Qed.

    Global Instance set_unfold_elem_of_event_list cd x :
      SetUnfoldElemOf x (event_list cd) (cd !! x.1 = Some x.2).
    Proof. tcclean. destruct x. symmetry. apply event_list_match. Qed.

    Lemma event_list_NoDup1 cd : NoDup (event_list cd).*1.
    Proof.
      unfold event_list.
      rewrite fmap_unfold.
      cbn.
      apply NoDup_bind;
        [set_unfold; hauto lq:on rew:off | idtac | apply NoDup_enumerate].
      intros [? ?] ?.
      apply NoDup_bind;
        [set_unfold; hauto lq:on rew:off | idtac | apply NoDup_enumerate].
      intros [? [? ?]] ?.
      apply NoDup_bind;
        [set_unfold; hauto lq:on rew:off | idtac | apply NoDup_enumerate].
      intros [? [? ?]] ?.
      auto with nodup.
    Qed.

    Lemma event_list_NoDup cd : NoDup (event_list cd).
    Proof. eapply NoDup_fmap_1. apply event_list_NoDup1. Qed.

    Definition event_map (cd : t) : gmap EID.t iEvent :=
      event_list cd |> list_to_map.


    Lemma event_map_match cd eid : (event_map cd) !! eid = cd !! eid.
    Proof.
      unfold event_map.
      destruct (cd !! eid) eqn: Heq.
      - apply elem_of_list_to_map.
        + apply event_list_NoDup1.
        + set_solver.
      - apply not_elem_of_list_to_map_1.
        set_solver.
    Qed.

    Global Instance lookup_unfold_event_map x cd R :
      LookupUnfold x cd R → LookupUnfold x (event_map cd) R.
    Proof. tcclean. apply event_map_match. Qed.


    (*** Accessors ***)

    Definition collect_all (P : EID.t -> iEvent -> Prop)
      `{∀ eid event, Decision (P eid event)}
      (cd : t) : gset EID.t :=
      filter (fun '(eid, event) => P eid event) (event_list cd)
        |> map fst |> list_to_set.
    Global Instance set_elem_of_collect_all eid P
      `{∀ eid event, Decision (P eid event)} cd :
      SetUnfoldElemOf eid (collect_all P cd) (∃x, cd !! eid = Some x ∧ P eid x).
    Proof. tcclean. set_unfold. hauto db:pair. Qed.
    Global Typeclasses Opaque collect_all.

    (** Get the set of all valid EID for that candidate *)
    Definition valid_eids (cd : t) :=
      collect_all (fun _ _ => true) cd.

    Global Instance set_elem_of_valid_eids eid cd :
      SetUnfoldElemOf eid (valid_eids cd) (∃ x, cd !! eid = Some x).
    Proof. tcclean. set_unfold. hauto db:pair. Qed.
    Global Typeclasses Opaque valid_eids.

    Definition is_reg_read (event : iEvent) : Prop :=
      match event with
      | IEvent (RegRead _ _) _ => true
      | _ => false
      end.

    Global Instance is_reg_read_decision event : (Decision (is_reg_read event)).
    Proof. unfold is_reg_read. apply _. Qed.

    (** Get the set of all register reads *)
    Definition reg_reads (cd : t) :=
      collect_all (λ _ event, is_reg_read event) cd.

    Definition is_reg_write (event : iEvent) : Prop :=
      match event with
      | IEvent (RegWrite _ _ _ _) _ => true
      | _ => false
      end.

    Global Instance is_reg_write_decision event : (Decision (is_reg_write event)).
    Proof. unfold is_reg_write. apply _. Qed.

    (** Get the set of all register writes *)
    Definition reg_writes (cd : t) :=
      collect_all (λ _ event, is_reg_write event) cd.

    Definition is_mem_read (event : iEvent) : Prop :=
      match event with
      | IEvent (MemRead _ _) _ => true
      | _ => false
      end.

    Global Instance is_mem_read_decision event : (Decision (is_mem_read event)).
    Proof. unfold is_mem_read. apply _. Qed.

    (** Get the set of all memory reads *)
    Definition mem_reads (cd : t) :=
      collect_all (λ _ event, is_mem_read event) cd.

    Definition is_mem_write (event : iEvent) :=
      match event with
      | IEvent (MemWrite _ _) _ => true
      | _ => false
      end.

    Global Instance is_mem_write_decision event : (Decision (is_mem_write event)).
    Proof. unfold is_mem_write. apply _. Qed.

    (** Get the set of all memory writes *)
    Definition mem_writes (cd : t) :=
      collect_all (λ _ event, is_mem_write event) cd.

    Definition is_mem_event (event : iEvent) : Prop :=
      match event with
      | IEvent (MemRead _ _) _ => true
      | IEvent (MemWrite _ _) _ => true
      | _ => false
      end.

    Global Instance is_mem_event_decision event : (Decision (is_mem_event event)).
    Proof. unfold is_mem_event. apply _. Qed.

    (** Get the set of all memory writes *)
    Definition mem_events (cd : t) :=
      collect_all (λ _ event, is_mem_event event) cd.

    Definition is_branch (event : iEvent) : Prop :=
      match event with
      | IEvent (BranchAnnounce _ _) _ => true
      | _ => false
      end.

    Global Instance is_branch_decision event : (Decision (is_branch event)).
    Proof. unfold is_branch. apply _. Qed.

    (** Get the set of all branches *)
    Definition branches (cd : t) :=
      collect_all (λ _ event, is_branch event) cd.

    (** Get the content of a barrier, returns none if not a barrier (or is an
        invalid EID) *)
    Definition get_barrier (event : iEvent) : option barrier:=
      match event with
      | IEvent (Barrier b) () => Some b
      | _ => None
      end.

    (** Get the set of all barriers *)
    Definition barriers (cd : t) :=
      collect_all (λ _ event, is_Some (get_barrier event)) cd.

    (** Get the content of a TLB operation, returns none if not a TLB operation
        (or is an invalid EID) *)
    Definition get_tlbop (event : iEvent) : option tlb_op :=
      match event with
      | IEvent (TlbOp _ to) () => Some to
      | _ => None
      end.

    (** Get the set of all TLB operations *)
    Definition tlpops (cd : t) :=
      collect_all (λ _ event, is_Some (get_tlbop event)) cd.

    (*** Utility relations ***)

    (** Intra instruction order *)
    Definition iio (cd : t) := po cd ∩ si cd.

    (** NOTE: make the dependencies opaque, and directly define wellformedness
        conditions for them for now *)
    Definition addr (cd : t) :=
      ⦗mem_reads cd⦘⨾
        (⦗mem_reads cd⦘ ∪ (iio_data cd ⨾ (rrf cd ∪ ⦗reg_writes cd⦘))⁺)⨾
        iio_addr cd⨾
        ⦗mem_events cd⦘.
    Global Typeclasses Opaque addr.

    Definition data (cd : t) :=
      ⦗mem_reads cd⦘⨾
        (⦗mem_reads cd⦘ ∪ (iio_data cd ⨾ (rrf cd ∪ ⦗reg_writes cd⦘))⁺)⨾
        iio_data cd⨾
        ⦗mem_events cd⦘.
    Global Typeclasses Opaque data.

    Definition ctrl (cd : t) :=
      ⦗mem_reads cd⦘⨾
        (⦗mem_reads cd⦘ ∪ (iio_data cd ⨾ (rrf cd ∪ ⦗reg_writes cd⦘))⁺)⨾
        iio_ctrl cd⨾
        ⦗branches cd⦘⨾
        (po cd ∖ si cd).
    Global Typeclasses Opaque ctrl.


    Definition gather_by_key_aux `{Countable K} (cd : t) (b : gmap K (gset EID.t))
      (P : EID.t -> iEvent -> option K) :=
      fold_left (λ acc '(eid, event), (match (P eid event) with
                                       | Some k => {[ k := {[eid]}]}
                                       | None =>  ∅
                                       end) ∪ₘ acc) (event_list cd) b.

    (** This helper computes an optional key from each eid and event pair of a
        candidate using [get_key], and gathers all eids with the same key
        together into a set. It returns a map from keys to sets of eids *)
    Definition gather_by_key `{Countable K} (cd : t)
      (get_key : EID.t -> iEvent -> option K) :=
      gather_by_key_aux cd (∅ : gmap K (gset EID.t)) get_key.

    Lemma lookup_total_unfold_gather_by_key_aux `{Countable K} (cd : t)
      (get_key : EID.t -> iEvent -> option K) (b : gmap K (gset EID.t)) (k: K):
      (forall k, b !!! k ## collect_all (λ _ _, true) cd) ->
      gather_by_key_aux cd b get_key !!! k =
      (b !!! k ∪ collect_all (λ eid event, (get_key eid event) =? Some k) cd).
    Proof.
      unfold gather_by_key_aux, valid_eids, collect_all. revert b.
      pose proof (event_list_NoDup1 cd) as Hdup.

      induction (event_list cd); first set_solver.
      assert (map fst (filter (λ '(_, _), True) l) = l.*1) as Heql.
      { clear. induction l; first done.
        rewrite filter_cons_True. hauto lq:on use: map_cons. hauto. }

      destruct a as [eid event].
      rewrite fmap_cons in Hdup. specialize (IHl (NoDup_cons_1_2 _ _ Hdup)).
      apply NoDup_cons_1_1 in Hdup.
      do 2 rewrite filter_cons; simpl.

      intros b Hb;simpl. rewrite IHl.
      - destruct (get_key eid event);
          (case_decide as Hk;[rewrite bool_unfold in Hk; inversion Hk; subst|]).
        + rewrite lookup_total_unfold; set_solver + Hb.
        + assert (k ≠ k0) as Hnk by naive_solver.
          rewrite lookup_total_unfold; set_solver + Hb.
        + rewrite lookup_total_unfold; set_solver +.
      - intros k'. case_match eqn:PP.
        + destruct (decide (k0 = k')).
          * subst k0. rewrite lookup_total_unfold.
            rewrite Heql. rewrite Heql in Hb. set_solver + Hb Hdup.
          * rewrite lookup_total_unfold; set_solver + Hb.
        + rewrite lookup_total_unfold; set_solver + Hb.
    Qed.

    (** The set of eids with key [k] in the gathered map generated with [get_key]
        is equiv to the set of all eids filtered with [get_key] *)
    Lemma lookup_total_unfold_gather_by_key `{Countable K} (cd : t)
      (get_key : EID.t -> iEvent -> option K) (k: K):
      gather_by_key cd get_key !!! k =
      collect_all (λ eid event, (get_key eid event) =? Some k) cd.
    Proof.
      rewrite lookup_total_unfold_gather_by_key_aux.
      rewrite lookup_total_empty. set_solver +.
      intros. rewrite lookup_total_empty. set_solver +.
    Qed.

    Global Instance set_elem_of_gather_by_key_lookup `{Countable K} (cd : t)
      (get_key : EID.t -> iEvent -> option K) (k: K) (eid : EID.t):
      SetUnfoldElemOf eid (gather_by_key cd get_key !!! k)
        (∃ E, cd !! eid = Some E ∧ get_key eid E = Some k).
    Proof.
      tcclean. rewrite lookup_total_unfold_gather_by_key. set_unfold.
      split; intros [? Heq]. rewrite bool_unfold in Heq. all:hauto.
    Qed.

    Lemma lookup_is_Some_gather_by_key_aux `{Countable K} (cd : t)
      (get_key : EID.t -> iEvent -> option K) (k: K) b:
      (is_Some (b !! k) ∨ ∃ eid event, (eid, event) ∈ event_list cd
                                       ∧ get_key eid event = Some k) ->
       is_Some((gather_by_key_aux cd b get_key) !! k).
    Proof.
      unfold gather_by_key_aux. revert b.
      induction (event_list cd); intros ? Hinit; first set_solver.
      simpl. destruct a as [eid event]. destruct Hinit as [Hinit|Hinit].
      apply IHl. destruct Hinit. left. case_match. destruct (decide (k = k0)).
      subst k0. exists ({[eid]} ∪ x).
      assert (Some {[eid]} ∪ₒ Some x = Some ({[eid]} ∪ x)) as <-. done.
      apply lookup_unfold_pointwise_union. tcclean.
      rewrite lookup_singleton_Some; hauto. done.
     + exists x. assert (None ∪ₒ Some x = Some x) as <-. done.
       apply lookup_unfold_pointwise_union. tcclean.
       rewrite lookup_singleton_None; hauto. done.
     + exists x. assert (None ∪ₒ Some x = Some x) as <-. done.
       apply lookup_unfold_pointwise_union. tcclean.
       rewrite lookup_empty; hauto. done.
     + destruct Hinit as (?&?&Hcons&HP).
       rewrite elem_of_cons in Hcons. destruct Hcons as [Hhd | Hin].
       inversion Hhd; subst.
       * rewrite HP. apply IHl. left.
         destruct (b !! k) eqn:Hb.
         exists ({[eid]} ∪ g).
         assert (Some {[eid]} ∪ₒ Some g = Some ({[eid]} ∪ g)) as <-. done.
         apply lookup_unfold_pointwise_union. tcclean.
         rewrite lookup_singleton_Some; hauto. done.
         exists {[eid]}. assert (Some {[eid]} ∪ₒ None = Some {[eid]}) as <-. done.
         apply lookup_unfold_pointwise_union. tcclean.
         rewrite lookup_singleton_Some; hauto. done.
       * apply IHl. right. do 2 eexists. naive_solver.
    Qed.

    (** if exists an event with key [k], them [k] must in the gathered map *)
    Lemma lookup_is_Some_gather_by_key `{Countable K} (cd : t)
      (get_key : EID.t -> iEvent -> option K) (k: K):
      (∃ eid event, (eid, event) ∈ event_list cd ∧ get_key eid event = Some k) ->
       is_Some((gather_by_key cd get_key) !! k).
    Proof.
      unfold gather_by_key. intro Hexists.
      apply lookup_is_Some_gather_by_key_aux. right; hauto.
    Qed.

    (** returns a symmetric relation, such that two events in the relation have
        the same key computed with [get_key] *)
    Definition sym_rel_with_same_key `{Countable K} (cd : t)
      (get_key : EID.t -> iEvent -> option K) :=
      let map : gmap K (gset EID.t) :=
        gather_by_key cd get_key in
      map_fold (fun (k : K) (s : gset EID.t) (r : grel EID.t) => r ∪ (s × s))
        ∅ map.

    (** A local unfold instance for [map_fold] with an union combinator which is
        used in [sym_rel_by_key] *)
    Local Instance set_elem_of_map_fold_set_union `{Countable K, Countable K'}
      {V} (m : gmap K V) b e (f : K -> V -> gset K') :
      SetUnfoldElemOf (e)
        (map_fold (fun (k: K) (v : V) (r : gset K') => r ∪ (f k v)) b m)
        (e ∈ b ∨ ∃ k v, m !! k = Some v ∧ e ∈ (f k v)).
    Proof.
      tcclean. cinduction m using map_fold_cind.
      hauto lq:on use:lookup_empty_Some.
      set_unfold. setoid_rewrite H2; clear H2.
      split.
      - intros [[| (?&?&?&?)]|]; first hauto lq:on;
          (destruct (decide (e ∈ b)); [hauto lq:on | right; do 2 eexists;
                                                     rewrite lookup_insert_Some;
                                                     sauto lq:on]).
      - intros [|(?&?&Hlk&?)]; first hauto lq:on;
          rewrite lookup_insert_Some in Hlk; hauto lq:on.
    Qed.

    (** An unfold instance for [sym_rel_by_key] *)
    Global Instance set_elem_of_sym_rel_with_same_key `{Countable K} cd
      get_key eid1 eid2 :
      SetUnfoldElemOf (eid1, eid2)
        (sym_rel_with_same_key cd get_key)
        (∃ E1 E2 (k: K), cd !! eid1 = Some E1 ∧ cd !! eid2 = Some E2
                         ∧ get_key eid1 E1 = Some k ∧ get_key eid2 E2 = Some k).
    Proof.
      tcclean. set_unfold.
      split.
      - intros [|(k&?&Hfold&?)]; first done.
        pose proof (lookup_total_unfold_gather_by_key cd get_key k) as Hunfold.
        rewrite lookup_total_alt in Hunfold. rewrite Hfold in Hunfold. set_unfold.
        pose proof (Hunfold eid1) as [(E1 & Hlk1 & Heq1) _]; first set_solver.
        pose proof (Hunfold eid2) as [(E2 & Hlk2 & Heq2) _]; first set_solver.
        repeat rewrite bool_unfold in *.
        hauto lq:on.
      - intros (?&?&k&Hlk1&Hloc1&?&Hloc2); right.
        opose proof* (lookup_is_Some_gather_by_key cd get_key k) as HSome.
        set_unfold. hauto.
        destruct HSome as [? HSome].
        pose proof (lookup_total_unfold_gather_by_key cd get_key k) as Hunfold.
        rewrite lookup_total_alt in Hunfold.
        rewrite HSome in Hunfold. simpl in Hunfold.
        do 2 eexists. split.
        + eassumption.
        + set_unfold. do 2 rewrite Hunfold.
          split;eexists;(split;[eassumption|rewrite bool_unfold;hauto lq:on]).
    Qed.

    (** get physical address of an event *)
    Definition get_pa (e : iEvent) : option (Arch.pa):=
      match e with
      | IEvent (MemRead _ rr) _ => Some (rr.(ReadReq.pa))
      | IEvent (MemWrite n rr) _ => Some (rr.(WriteReq.pa))
      | _ => None
      end.

    (** Symmetry relation referring to events having the same address.
        Might need to be updated for mixed-size *)
    Definition loc (cd : t) : grel EID.t :=
      sym_rel_with_same_key cd (λ _ event, get_pa event).

    (** Symmetry relation referring to events of a same thread *)
    Definition sthd (cd : t) : grel EID.t :=
      sym_rel_with_same_key cd (λ eid _, Some (eid.(EID.tid))).

  End Candidate.

  (** Non-mixed size well-formedness *)
  Module NMSWF.
    Import Candidate.

    (** Get 8 bytes values*)
    Definition get_val (event : iEvent) :=
      match event : iEvent with
      | IEvent (MemRead 8 rr) (inl (val, _)) =>
          Some val
      | IEvent (MemWrite 8 rr) _ =>
          Some (rr.(WriteReq.value))
      | _ => None
      end.

    (** This relation only make sense for 8-bytes non-mixed-size models.
        It relates events with the same values *)
    Definition val (cd : t) : grel EID.t :=
      sym_rel_with_same_key cd (λ _ event, get_val event).

    Definition co_wf (cd : t) : bool :=
      let co := co cd in
      let loc := loc cd in
      let writes := mem_writes cd in
      bool_decide (grel_irreflexive co) &&
        bool_decide (grel_transitive co) &&
        bool_decide (co ⊆ loc) &&
        bool_decide (grel_dom co ⊆ writes) &&
        bool_decide (grel_rng co ⊆ writes) &&
        (loc ∩ (writes × writes) =? co ∪ co⁻¹ ∪ ⦗writes⦘).

    Definition rf_wf (cd : t) : bool :=
      let rf := rf cd in
      let loc := loc cd in
      let val := val cd in
      let reads := mem_reads cd in
      let writes := mem_writes cd in
      bool_decide (grel_dom rf ⊆ reads) &&
        bool_decide (grel_rng rf ⊆ writes) &&
        bool_decide (grel_functional (rf⁻¹)) &&
        bool_decide (rf ⊆ loc ∩ val).
    (* TODO incomplete *)

    (* Definition last_reg_access : gmap reg EID.t. *)

    Module IIO.
      Record t :=
        make {
            last_reg_access : gmap reg EID.t;
            last_reg_read : list EID.t;
            last_mem_reads : list EID.t;
            iio_data : grel EID.t;
            iio_addr : grel EID.t;
            iio_ctrl : grel EID.t;
          }.

      #[global] Instance eta : Settable _ :=
        settable! make
        <last_reg_access; last_reg_read; last_mem_reads; iio_data; iio_addr; iio_ctrl>.

      Definition init := make ∅ ∅ ∅ ∅.

      Definition reset_thread := setv last_reg_access ∅.

      (* WIP *)

      (* Notation "'for' x 'in' l 'with' a 'do' E 'on' i 'end'" := *)
      (*   (fold_left (fun a x => E) l i) *)
      (*     (at level 200, i at level 100, x binder, right associativity, only parsing). *)


      (* Definition eval_DepOn (iio : t) (deps : DepOn.t) : gset EID.t := *)
      (*   match deps with *)
      (*   | None => list_to_set iio.(last_reg_read) ∪ *)
      (*              list_to_set iio.(last_mem_reads) *)


      (*   for reg in deps.(DepOn.regs) with res do *)
      (*     (option_to_set $ iio.(last_reg_access) !! reg) ∪ res *)
      (*   on *)
      (*     for read_num in deps.(DepOn.mem_reads) with res do *)
      (*       (option_to_set $ iio.(last_mem_reads) !! read_num) ∪ res *)
      (*     on ∅ end *)
      (*   end. *)

      (* Definition iio_recompute (cd : t) := *)
      (*   for '(tid, traces) in enumerate cd.(events) with iio do *)
      (*     for '(iid, (trace, trace_end)) in traces with iio do *)
      (*       for '(num, event) in trace with iio do *)
      (*         let eid := EID.make tid iid num in *)
      (*         match event with *)
      (*         | IEvent (RegRead reg _) _ => *)
      (*             set last_reg_access <[reg := num]> iio *)
      (*         | IEvent (RegWrite reg _ deps _) _ => *)
      (*             iio *)
      (*               |> set last_reg_access <[reg := num]> *)
      (*               |> set iio_data (.∪ eval_DepOn iio deps) *)
      (*         | IEvent (MemRead n rr) _ => *)
      (*             iio *)
      (*               |> set iio_addr (.∪ eval_DepOn iio rr.(ReadReq.addr_dep_on)) *)
      (*         end *)
      (*       on iio done *)
      (*     on iio done *)
      (*   on iio done. *)


      (*         let *)


      (*   fold_left (fun '(tid, traces) => *)
      (*     fold_left (fun '(iid, (trace, trace_end)) => *)
      (*       fold_left (fun '(num, event) iio => *)
      (*         let eid := EID.make tid iid num in *)
      (*         match event with *)
      (*         | IEvent (RegRead reg _) _ => *)
      (*             set last_reg_access <[reg := num]> iio *)
      (*         | IEvent (RegWrite reg _ deps) _ => *)
      (*             iio *)
      (*               |> set last_reg_access <[reg := num]> *)
      (*               |> set iio_data (.∪ eval_DepOn iio deps) *)
      (*         | IEvent (MemRead n rr) _ => *)
      (*             iio *)
      (*               |> set iio_addr (.∪ eval_DepOn iio rr.(ReadReq.addr_dep_on)) *)



      (*                       (<[reg:= num]> last_reg_access, iio_addr, iio_data, iio_ctrl) *)


      (*               ) trace *)
      (*          ) traces ∘ reset_thread *)
      (*     ) enumerate cd.(events) init *)



      (*     for '(num, event) in enumerate trace *)
      (*         with '(last_reg_access, iio_addr, iio_data, iio_ctrl) do *)








    (* Check that a candidate is self consistent *)
    (* Definition wf (cd : t) : bool := *)

    End IIO.


  End NMSWF.



End CandidateExecutions.
