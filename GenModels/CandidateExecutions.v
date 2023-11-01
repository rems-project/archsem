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

Require Import SSCCommon.Options.
Require Import SSCCommon.Common.
Require Import SSCCommon.Exec.
Require Import SSCCommon.GRel.
Require Import SSCCommon.FMon.

Require Import ISASem.Interface.
Require Import ISASem.Deps.
Require Import TermModels.

Open Scope Z_scope.
Open Scope stdpp_scope.

(* Module to be imported *)
Module CandidateExecutions (IWD : InterfaceWithDeps) (Term : TermModelsT IWD).
  Import IWD.
  Import Term.
  Notation outcome := (IWD.outcome DepOn.t).
  Notation iMon := (IWD.iMon DepOn.t).
  Notation iSem := (IWD.iSem DepOn.t).
  Notation iEvent := (IWD.iEvent DepOn.t).
  Notation iTrace := (IWD.iTrace DepOn.t).

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

  (* Namespace *)
  (* TODO rename to Cand ? *)
  Module Candidate.
  Section Cand.
    Context {nmth : nat}.

    Record t :=
      make {
          (** Initial state *)
          init : MState.t nmth;
          (** Each thread is a list of instruction who each have a trace,
              we force the return type to be unit, but it just means we
              forget the actual value *)
          events : vec (list (iTrace ())) nmth;
          (* TODO po can be deduced by the order of events in the trace *)
          (** Program order. The per-thread order of all events in the trace *)
          generic_po : grel EID.t;
          (** Generic memory read from *)
          generic_rf : grel EID.t;
          (** Generic casual order *)
          generic_co : grel EID.t;
          (** Load-reserve/store conditional pair *)
          lxsx : grel EID.t;
          (** Atomic modify: relates reads and writes emitted by atomic rmw instructions *)
          amo : grel EID.t;
          (** Register read from (needed because of potentially relaxed register) *)
          rrf : grel EID.t;
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
      ∀ tid : fin nmth,
      ∀'trc ∈ cd.(events) !!! tid,
      iTrace_match isem trc.

    #[global] Instance ISA_match_dec cd isem : Decision (ISA_match cd isem).
    Proof using. solve_decision. Qed.

    (** Get an event at a given event ID in a candidate *)
    Global Instance lookup_eid : Lookup EID.t iEvent t :=
      fun eid cd =>
        traces ← cd.(events) !! eid.(EID.tid);
        '(trace, result) ← traces !! eid.(EID.iid);
        trace !! eid.(EID.num).

    (** This true if one of the instruction had an ISA model failure like a Sail
        assertion or an Isla assumption that failed. Due to out of order
        effects, an error might not be from the last instruction. *)
    Definition ISA_failed (cd : t) :=
      ∃'thread ∈ (vec_to_list cd.(events)), ∃'instr ∈ thread, is_Error instr.2.

    #[global] Instance ISA_failed_dec (cd : t) : Decision (ISA_failed cd).
    Proof using. solve_decision. Qed.

    Definition event_list (cd : t) : list (EID.t*iEvent) :=
      '(tid, traces) ← enumerate cd.(events);
      '(iid, (trace, trace_end)) ← enumerate traces;
       '(num, event) ← enumerate trace;
       [(EID.make tid iid num, event)].

    Global Typeclasses Opaque event_list.

    Import SetUnfoldPair.

    Lemma event_list_match cd eid ev :
      cd !! eid = Some ev ↔ (eid, ev) ∈ event_list cd.
    Proof using.
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
    Proof using . tcclean. destruct x. symmetry. apply event_list_match. Qed.

    Lemma event_list_NoDup1 cd : NoDup (event_list cd).*1.
    Proof using.
      unfold event_list.
      rewrite fmap_unfold.
      cbn.
      apply NoDup_bind;
        [set_unfold; hauto l:on | idtac | apply NoDup_enumerate].
      intros [? ?] ?.
      apply NoDup_bind;
        [set_unfold; hauto l:on | idtac | apply NoDup_enumerate].
      intros [? [? ?]] ?.
      apply NoDup_bind;
        [set_unfold; hauto l:on | idtac | apply NoDup_enumerate].
      intros [? [? ?]] ?.
      auto with nodup.
    Qed.

    Lemma event_list_NoDup cd : NoDup (event_list cd).
    Proof using. eapply NoDup_fmap_1. apply event_list_NoDup1. Qed.

    Definition event_map (cd : t) : gmap EID.t iEvent :=
      event_list cd |> list_to_map.


    Lemma event_map_match cd eid : (event_map cd) !! eid = cd !! eid.
    Proof using.
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
    Proof using. tcclean. apply event_map_match. Qed.


    (** * Accessors ***)

    Definition collect_all (P : EID.t -> iEvent -> Prop)
      `{∀ eid event, Decision (P eid event)}
      (cd : t) : gset EID.t :=
      filter (fun '(eid, event) => P eid event) (event_list cd)
        |> map fst |> list_to_set.
    Global Instance set_elem_of_collect_all eid P
      `{∀ eid event, Decision (P eid event)} cd :
      SetUnfoldElemOf eid (collect_all P cd) (∃x, cd !! eid = Some x ∧ P eid x).
    Proof using. tcclean. set_unfold. hauto db:pair. Qed.
    Global Typeclasses Opaque collect_all.

    (** Get the set of all valid EID for that candidate *)
    Definition valid_eids (cd : t) :=
      collect_all (fun _ _ => True) cd.

    Global Instance set_elem_of_valid_eids eid cd :
      SetUnfoldElemOf eid (valid_eids cd) (∃ x, cd !! eid = Some x).
    Proof using. tcclean. set_unfold. hauto db:pair. Qed.
    Global Typeclasses Opaque valid_eids.

    Definition is_reg_read (event : iEvent) : Prop :=
      match event with
      | RegRead _ _ &→ _ => True
      | _ => False
      end.

    Global Instance is_reg_read_decision event : (Decision (is_reg_read event)).
    Proof using. unfold is_reg_read. apply _. Qed.

    (** Get the set of all register reads *)
    Definition reg_reads (cd : t) :=
      collect_all (λ _ event, is_reg_read event) cd.

    Definition is_reg_write (event : iEvent) : Prop :=
      match event with
      | RegWrite _ _ _ _ &→ _ => True
      | _ => false
      end.

    Global Instance is_reg_write_decision event : (Decision (is_reg_write event)).
    Proof using. unfold is_reg_write. apply _. Qed.

    (** Get the set of all register writes *)
    Definition reg_writes (cd : t) :=
      collect_all (λ _ event, is_reg_write event) cd.

    Definition is_mem_read (event : iEvent) : Prop :=
      match event with
      | MemRead _ _ &→ _ => True
      | _ => False
      end.

    Global Instance is_mem_read_decision event : (Decision (is_mem_read event)).
    Proof using. unfold is_mem_read. apply _. Qed.

    (** Get the set of all memory reads *)
    Definition mem_reads (cd : t) :=
      collect_all (λ _ event, is_mem_read event) cd.

    Definition is_mem_write (event : iEvent) :=
      match event with
      | MemWrite _ _ &→ _ => True
      | _ => False
      end.

    Global Instance is_mem_write_decision event : (Decision (is_mem_write event)).
    Proof using. unfold is_mem_write. apply _. Qed.

    (** Get the set of all memory writes *)
    Definition mem_writes (cd : t) :=
      collect_all (λ _ event, is_mem_write event) cd.

    Definition is_mem_event (event : iEvent) : Prop :=
      match event with
      | MemRead _ _ &→ _ => True
      | MemWrite _ _ &→ _ => True
      | _ => False
      end.

    Global Instance is_mem_event_decision event : (Decision (is_mem_event event)).
    Proof using. unfold is_mem_event. apply _. Qed.

    (** Get the set of all memory writes *)
    Definition mem_events (cd : t) :=
      collect_all (λ _ event, is_mem_event event) cd.

    Definition is_branch (event : iEvent) : Prop :=
      match event with
      | BranchAnnounce _ _ &→ _ => True
      | _ => False
      end.

    Global Instance is_branch_decision event : (Decision (is_branch event)).
    Proof using. unfold is_branch. apply _. Qed.

    (** Get the set of all branches *)
    Definition branches (cd : t) :=
      collect_all (λ _ event, is_branch event) cd.

    (** Get the content of a barrier, returns none if not a barrier (or is an
        invalid EID) *)
    Definition get_barrier (event : iEvent) : option barrier:=
      match event with
      | Barrier b &→ () => Some b
      | _ => None
      end.

    (** Get the set of all barriers *)
    Definition barriers (cd : t) :=
      collect_all (λ _ event, is_Some (get_barrier event)) cd.

    (** Get the content of a TLB operation, returns none if not a TLB operation
        (or is an invalid EID) *)
    Definition get_tlbop (event : iEvent) : option tlb_op :=
      match event with
      | TlbOp _ to &→ () => Some to
      | _ => None
      end.

    (** Get the set of all TLB operations *)
    Definition tlbops (cd : t) :=
      collect_all (λ _ event, is_Some (get_tlbop event)) cd.

    (** Get the content of a cache operation, returns none if not a cache operation
        (or is an invalid EID) *)
    Definition get_cacheop (event : iEvent) : option cache_op :=
      match event with
      | CacheOp _ co &→ () => Some co
      | _ => None
      end.

    (** Get the set of all cache operations *)
    Definition cacheops (cd : t) :=
      collect_all (λ _ event, is_Some (get_cacheop event)) cd.


    (** * Connection to final state *)

    (** Get the list of final register values in a candidate for a thread *)
    Definition final_reg_gmap_tid (cd : t) (tid : fin nmth) :
      gmap reg reg_type :=
      foldl (λ umap itrc,
          foldl (λ umap ev,
              match ev with
              | RegWrite reg _ _ val &→ _ => <[reg := val]> umap
              | _ => umap
              end
            ) umap itrc.1
        ) (∅ : gmap reg reg_type) (cd.(events) !!! tid).


    (** Get the final register maps of all threads from a candidate *)
    Definition final_reg_map_tid (cd : t) (tid : fin nmth) :
        registerMap :=
      let umap := final_reg_gmap_tid cd tid in
      λ reg,
        match umap !! reg with
        | Some val => val
        | None => (cd.(init).(MState.regs) !!! tid) reg
        end.

    (** Get all the final register map from candidate *)
    Definition final_reg_map (cd : t) : vec registerMap nmth :=
      fun_to_vec (final_reg_map_tid cd).

    (** Get the last write for each pa in candidate. If it's not in the map, it
        was not written by the candidate *)
    Definition final_write_per_pa (cd : t) : gmap pa (EID.t * bv 8) :=
      foldl
        (λ mmap '(eid, ev),
          match ev with
          | MemWrite n wr &→ _ =>
              foldl
                (λ mmap i,
                  let pa := pa_addZ (WriteReq.pa wr) (Z.of_nat i) in
                  let byte := bv_get_byte 8 (N.of_nat i) (WriteReq.value wr) in
                  match mmap !! pa with
                  | Some (eid', _) =>
                      match decide ((eid, eid') ∈ cd.(generic_co)) with
                      | left _ => mmap
                      | right _ => <[pa := (eid, byte)]> mmap
                      end
                  | None => <[pa := (eid, byte)]> mmap
                  end) mmap (seq 0 (N.to_nat n))
          | _ => mmap
          end) ∅ (event_list cd).

    Definition final_mem_map (cd : t) : memoryMap :=
      let mmap := final_write_per_pa cd in
      λ pa,
        match mmap !! pa with
        | Some (_, val) => val
        | None => cd.(init).(MState.memory) pa
        end.

    Definition cd_to_MState (cd : t) : MState.t nmth :=
      {| MState.regs := final_reg_map cd; MState.memory := final_mem_map cd |}.

    Definition cd_to_MState_final (cd : t) (term : terminationCondition nmth) :
        option (MState.final nmth) :=
      MState.finalize (MState.MakeI (cd_to_MState cd) term).

    (** * Utility relations ***)

    (** This helper computes an optional key from each eid and event pair of a
        candidate using [get_key], and gathers all eids with the same key
        together into a set. It returns a map from keys to sets of eids *)
    Definition gather_by_key `{Countable K} (cd : t)
        (get_key : EID.t -> iEvent -> option K) : gmap K (gset EID.t) :=
      fold_left (λ acc '(eid, event), match get_key eid event with
                                       | Some k => {[ k := {[eid]}]}
                                       | None => ∅
                                       end ∪ₘ acc) (event_list cd) ∅.

    Global Instance set_elem_of_gather_by_key_lookup `{Countable K} (cd : t)
      (get_key : EID.t → iEvent → option K) (k: K) (eid : EID.t):
      SetUnfoldElemOf eid (gather_by_key cd get_key !!! k)
        (∃ E, cd !! eid = Some E ∧ get_key eid E = Some k).
    Proof.
      tcclean.
      unfold gather_by_key.
      orewrite* (fold_left_inv_ND
        (λ map tl, ∀ eid k,
           eid ∈ map !!! k ↔
             ∃ ev, cd !! eid = Some ev
                   ∧ (eid, ev) ∉ tl
                   ∧ get_key eid ev = Some k)).
      - apply event_list_NoDup.
      - clear eid k. intros eid k.
        rewrite lookup_total_unfold.
        setoid_rewrite event_list_match.
        set_solver.
      - clear eid k. intros map [eid ev] tl Hel Hntl Hinv eid' k.
        rewrite <- event_list_match in Hel.
        destruct (get_key eid ev) as [k' |] eqn:Hgk.
        1: destruct decide subst k k'.
        all: destruct decide subst eid eid'.
        all: rewrite lookup_total_unfold.
        all: set_unfold.
        all: rewrite Hinv.
        all: set_solver - Hinv.
      - set_solver.
    Qed.

    Global Instance lookup_total_unfold_gather_by_key `{Countable K} (cd : t)
        (get_key : EID.t → iEvent → option K) (k: K):
      LookupTotalUnfold k (gather_by_key cd get_key)
        (collect_all (λ eid event, get_key eid event = Some k) cd).
    Proof. tcclean. set_solver. Qed.


    Lemma gather_by_key_None `{Countable K} (cd : t)
        (get_key : EID.t → iEvent → option K) (k : K):
      gather_by_key cd get_key !! k = None ↔
      ∀ eid ev, (eid, ev) ∈ event_list cd → get_key eid ev ≠ Some k.
    Proof.
      unfold gather_by_key.
      orewrite* (fold_left_inv_ND
        (λ map tl, ∀ k,
           map !! k = None ↔
             ∀ eid ev, (eid, ev) ∈ event_list cd →
           (eid, ev) ∈ tl ∨ get_key eid ev ≠ Some k)).
      - apply event_list_NoDup.
      - clear k.
        intro k.
        rewrite lookup_unfold.
        hauto lq:on.
      - clear k. intros map [eid ev] tl Hel Hntl Hinv k.
        destruct (get_key eid ev) as [k' |] eqn:Hgk.
        1: destruct decide subst k k'.
        all: rewrite lookup_unfold.
        all: rewrite option_union_None.
        all: rewrite Hinv; clear Hinv.
        all: set_solver.
      - set_solver.
    Qed.

    (** If there is an event with key [k], then [k] must in the gathered map *)
    Lemma lookup_is_Some_gather_by_key `{Countable K} (cd : t)
        (get_key : EID.t → iEvent → option K) (k: K):
      (∃ eid event, (eid, event) ∈ event_list cd ∧ get_key eid event = Some k) →
       is_Some (gather_by_key cd get_key !! k).
    Proof.
      destruct (gather_by_key cd get_key !! k) eqn:Heqn.
      - done.
      - rewrite gather_by_key_None in Heqn.
        naive_solver.
    Qed.

    (** Returns a symmetric relation, such that two events are in the relation
        iff they have the same key computed with [get_key] *)
    Definition sym_rel_with_same_key `{Countable K} (cd : t)
      (get_key : EID.t -> iEvent -> option K) :=
      finmap_reduce_union (λ k s, s × s) (gather_by_key cd get_key).

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
      - intros (?&?&?&?).
        lookup_lookup_total; set_solver.
      - intros (?&?&k&?). destruct_and!.
        opose proof* (lookup_is_Some_gather_by_key cd get_key k) as [? HSome].
        { set_solver. }
        do 2 eexists.
        repeat split_and; first eassumption.
        all: lookup_lookup_total; set_solver.
    Qed.

    (** get physical address of an event *)
    Definition get_pa (e : iEvent) : option (Arch.pa):=
      match e with
      | MemRead _ rr &→ _ => Some (rr.(ReadReq.pa))
      | MemWrite n rr &→ _ => Some (rr.(WriteReq.pa))
      | _ => None
      end.

    (** Symmetry relation referring to events having the same address.
        Might need to be updated for mixed-size *)
    Definition loc (cd : t) : grel EID.t :=
      sym_rel_with_same_key cd (λ _ event, get_pa event).

    (** Symmetry relation referring to events of a same instruction *)
    Definition same_instruction (cd : t) : grel EID.t :=
      sym_rel_with_same_key cd (λ eid _, Some (eid.(EID.tid), eid.(EID.iid))).

    (** Symmetry relation referring to events of a same thread *)
    Definition int (cd : t) : grel EID.t :=
      sym_rel_with_same_key cd (λ eid _, Some (eid.(EID.tid))).

    (** Inter instruction order *)
    Definition instruction_order (cd : t) := generic_po cd ∖ same_instruction cd.

    (** Intra instruction order *)
    Definition iio (cd : t) := generic_po cd ∩ same_instruction cd.

    (** NOTE: make the dependencies opaque, and directly define wellformedness conditions for them for now *)
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
        (instruction_order cd ∖ same_instruction cd).
    Global Typeclasses Opaque ctrl.

    End Cand.
  End Candidate.
  Arguments Candidate.t : clear implicits.


  (** Non-mixed size well-formedness *)
  Module NMSWF.
    Import Candidate.
  Section NMSWF.
    Context {nmth : nat}.

    (** Get 8 bytes values*)
    Definition get_val (event : iEvent) :=
      match event : iEvent with
      | MemRead 8 rr &→ inl (val, _) =>
          Some val
      | MemWrite 8 rr &→ _ =>
          Some (rr.(WriteReq.value))
      | _ => None
      end.

    (** This relation only make sense for 8-bytes non-mixed-size models.
        It relates events with the same values *)
    Definition val8 (cd : t nmth) : grel EID.t :=
      sym_rel_with_same_key cd (λ _ event, get_val event).

    Definition is_not_size8 (event : iEvent) :Prop :=
      match event with
      | MemRead 8 _ &→ _ => False
      | MemRead _ _ &→ _ => True
      | MemWrite 8 _ &→ _ => False
      | MemWrite _ _ &→ _ => True
      | _ => False
      end.

    Global Instance is_not_size8_decision event : Decision (is_not_size8 event).
    Proof. unfold is_not_size8. apply _. Qed.
      
    (** Check that all memory accesses have size 8. Alignment checking need to
        know how pa work and thus need to be architecture specific*)
    Definition size8_wf (cd : t nmth) : Prop :=
      collect_all (λ _ event, is_not_size8 event) cd = ∅.

    (* Definition last_reg_access : gmap reg EID.t. *)

    (* Module IIO. *)
    (*   Record t := *)
    (*     make { *)
    (*         last_reg_access : gmap reg EID.t; *)
    (*         last_reg_read : list EID.t; *)
    (*         last_mem_reads : list EID.t; *)
    (*         iio_data : grel EID.t; *)
    (*         iio_addr : grel EID.t; *)
    (*         iio_ctrl : grel EID.t; *)
    (*       }. *)

    (*   #[global] Instance eta : Settable _ := *)
    (*     settable! make *)
    (*     <last_reg_access; last_reg_read; last_mem_reads; iio_data; iio_addr; iio_ctrl>. *)

    (*   Definition init := make ∅ ∅ ∅ ∅. *)

    (*   Definition reset_thread := setv last_reg_access ∅. *)

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

    (* End IIO. *)

    Section def.

    Context (cd : Candidate.t nmth).

    Notation "'generic_po'" := (generic_po cd).
    Notation "'generic_co'" := (generic_co cd).
    Notation "'generic_rf'" := (generic_rf cd).
    Notation "'loc'" := (loc cd).
    Notation "'val8'" := (val8 cd).
    Notation "'addr'" := (addr cd).
    Notation "'data'" := (data cd).
    Notation "'ctrl'" := (ctrl cd).
    Notation "'writes'" := (mem_writes cd).
    Notation "'reads'" := (mem_reads cd).
    Notation "'mevents'" := (mem_events cd).

    Record generic_co_wf' :=
      {
        generic_co_irr : grel_irreflexive generic_co;
        generic_co_trans : grel_transitive generic_co;
      }.

    Record generic_rf_wf' :=
      {
        grf_dom : grel_dom generic_rf ⊆ reads;
        grf_rng : grel_rng generic_rf ⊆ writes;
        grf_inv_func : grel_functional (generic_rf⁻¹);
        grf_in_loc_val : generic_rf ⊆ loc ∩ val8;
      }.

    Record generic_po_wf' :=
      {
        generic_po_irr : grel_irreflexive generic_po;
        generic_po_trans : grel_transitive generic_po;
        generic_po_total : generic_po ∪ generic_po⁻¹ = int cd;
      }.

    Record addr_wf' :=
      {
        addr_dom : grel_dom addr ⊆ reads;
        addr_rng : grel_rng addr ⊆ mevents;
        addr_in_instruction_order : addr ⊆ generic_po;
      }.

    Record data_wf' :=
      {
        data_dom : grel_dom data ⊆ reads;
        data_rng : grel_rng data ⊆ writes;
        data_in_instruction_order : data ⊆ generic_po;
      }.

    Record ctrl_wf' :=
      {
        ctrl_dom : grel_dom ctrl ⊆ reads;
        ctrl_in_instruction_order : ctrl ⊆ generic_po;
        ctrl_instruction_order_in_ctrl : ctrl⨾generic_po ⊆ ctrl;
      }.

    Record wf :=
      {
        generic_po_wf :> generic_po_wf';
        generic_co_wf :> generic_co_wf';
        generic_rf_wf :> generic_rf_wf';
        ctrl_wf :> ctrl_wf';
        data_wf :> data_wf';
        addr_wf :> addr_wf';
      }.
    End def.

  End NMSWF.
  End NMSWF.

  Module Ax.
    Import Candidate.
    Notation cand := t.
      (* Context {unspec : Type}. *)
      (* Notation mresult := (ModelResult.t unspec). *)
      (* Notation model := (Model.nc unspec). *)

    (** Behaviors an axiomatic model can give to a candidate *)
    Inductive behavior {unspec : Type} :=
    (** The candidate execution is allowed *)
    | Allowed
    (** The candidate execution is forbidden *)
    | Rejected
    (** The candidate execution leads to some unspecified behavior.
          Unspecified is any kind of behavior that is not fully specified but is
          not a model error. For example a BBM failure. *)
    | Unspecified (u : unspec).
    Arguments behavior : clear implicits.

    (** An axiomatic model is just a candidate classifier. *)
    Definition t unspec := ∀ n, cand n → result string (behavior unspec).

    Module Res.
      Section Res.
        Context {unspec : Type}.
        Notation axres := (result string (behavior unspec)).
        Notation mres := (Model.Res.t unspec).
        Notation model := (Model.nc unspec).

      Definition to_ModelResult (axr : axres) {n} (cd : cand n)
        (term : terminationCondition n) : option (mres n) :=
        match axr with
        | Ok Allowed => cd_to_MState_final cd term |$> Model.Res.FinalState
        | Ok Rejected => None
        | Ok (Unspecified u) => Some (Model.Res.Unspecified u)
        | Error msg => Some (Model.Res.Error msg)
        end.

      (** When a model gives a more precise definition for the error of another
      model. See [Model.wider]. This means axr' is wider than axr *)
      Definition wider (axr axr' : axres) :=
        match axr with
        | Ok x => axr' = Ok x
        | _ => True
        end.

      Definition weaker (axr axr' : axres) :=
        match axr, axr' with
        | _, Error _ => True
        | Ok Allowed, Ok Allowed => True
        | Ok Rejected, _ => True
        | Ok (Unspecified u), Ok (Unspecified u') => u = u'
        | _, _ => False
        end.

      Lemma wider_weaker (axr axr' : axres) : wider axr axr' → weaker axr' axr.
      Proof using. unfold wider, weaker. repeat case_split; naive_solver. Qed.

      Definition equiv (axr axr' : axres) :=
        match axr, axr' with
        | Ok val, Ok val' => val = val'
        | Error _, Error _ => True
        | _,_=> False
        end.

      Lemma equiv_weaker axr axr' :
        equiv axr axr' ↔ weaker axr axr' ∧ weaker axr' axr.
      Proof using. unfold equiv, weaker. repeat case_split; naive_solver. Qed.

      Lemma equiv_wider axr axr' :
        equiv axr axr' ↔ wider axr axr' ∧ (is_Ok axr' → is_Ok axr).
      Proof using. unfold equiv, wider. sauto lq:on. Qed.

      Lemma equiv_wider' axr axr' : equiv axr axr' → wider axr axr'.
      Proof using. rewrite equiv_wider. naive_solver. Qed.

      Lemma equiv_is_ok axr axr' :
        equiv axr axr' → (is_Ok axr ↔ is_Ok axr').
      Proof using. unfold equiv. sauto lq:on. Qed.
      End Res.
    End Res.

    Section Ax.
      Context {unspec : Type}.
      Notation axres := (result string (behavior unspec)).
      Notation mres := (Model.Res.t unspec).
      Notation model := (Model.nc unspec).
      Notation t := (t unspec).

      (** Lifting Res definition to Ax *)
      Definition wider (ax ax' : t) := ∀ n cd, Res.wider (ax n cd) (ax' n cd).
      Definition weaker (ax ax' : t) := ∀ n cd, Res.weaker (ax n cd) (ax' n cd).
      Definition equiv (ax ax' : t) := ∀ n cd, Res.equiv (ax n cd) (ax' n cd).
      Lemma wider_weaker (ax ax' : t) : wider ax ax' → weaker ax' ax.
      Proof using.
        unfold wider, weaker. intros. apply Res.wider_weaker. naive_solver.
      Qed.
      Lemma equiv_weaker (ax ax' : t) :
        equiv ax ax' ↔ weaker ax ax' ∧ weaker ax' ax.
      Proof using.
        unfold equiv, weaker. setoid_rewrite Res.equiv_weaker. naive_solver.
      Qed.

      Lemma equiv_wider (ax ax' : t) :
        equiv ax ax' ↔
          wider ax ax' ∧ (∀ n cd, is_Ok (ax' n cd) → is_Ok (ax n cd)).
      Proof using.
        unfold equiv, wider. setoid_rewrite Res.equiv_wider. naive_solver.
      Qed.
      Lemma equiv_wider' (ax ax' : t) :
        equiv ax ax' → wider ax ax'.
      Proof using. rewrite equiv_wider. naive_solver. Qed.
      Lemma equiv_is_ok (ax ax' : t) :
        equiv ax ax' → (∀ n cd, is_Ok (ax n cd) ↔ is_Ok (ax' n cd)).
      Proof using.
        unfold equiv. intros. apply Res.equiv_is_ok. naive_solver.
      Qed.

      Definition to_ModelResult (ax : t) {n} (cd : cand n)
        (term : terminationCondition n) : option (mres n) :=
        Res.to_ModelResult (ax n cd) cd term.

      (** Creates a non-computational model from an instruction semantic and an
          axiomatic model *)
      Definition to_Modelnc (isem : iMon ()) (ax : t) : model :=
        λ n initSt,
          {[ mr |
             ∃ cd : cand n,
               cd.(init) = initSt
               ∧ ISA_match cd isem
               ∧ to_ModelResult ax cd initSt.(MState.termCond) = Some mr
          ]}.

      Lemma wider_Model (isem : iMon ()) (ax ax' : t) :
        wider ax ax' → Model.wider (to_Modelnc isem ax) (to_Modelnc isem ax').
      Proof using.
        intros WD nmth initSt.
        split.
        all: intros NE.
        all: set_unfold.
        all: repeat split_and.
        all: intros ?.
        all: try split.
        all: intros [cd ?].
        all: specialize (WD nmth cd); unfold Res.wider.
        all: destruct (ax nmth cd) as [[]|] eqn:Heqn.
        all: destruct (ax' nmth cd) as [[]|] eqn:Heqn'.
        all: try (eapply NE; clear NE).
        all: (exists cd; intuition).
        all: unfold to_ModelResult, Res.to_ModelResult in *.
        all: rewrite Heqn in *.
        all: rewrite Heqn' in *.
        all: hauto l:on.
        Unshelve.
        all: exact "".
      Qed.

      Lemma weaker_Model (isem : iMon ()) (ax ax' : t) :
        weaker ax ax' → Model.weaker (to_Modelnc isem ax) (to_Modelnc isem ax').
      Proof using.
        intros WD nmth initSt.
        intros NE.
        repeat split_and.
        all: set_unfold.
        all: intros ? [cd ?].
        all: specialize (WD nmth cd); unfold Res.weaker.
        all: destruct (ax nmth cd) as [[]|] eqn:Heqn.
        all: destruct (ax' nmth cd) as [[]|] eqn:Heqn'.
        all: try (eapply NE; clear NE).
        all: (exists cd; intuition).
        all: unfold to_ModelResult, Res.to_ModelResult in *.
        all: rewrite Heqn in *.
        all: rewrite Heqn' in *.
        all: hauto l:on.
        Unshelve.
        all: exact "".
      Qed.

      Lemma equiv_Model (isem : iMon ()) (ax ax' : t) :
        equiv ax ax' → Model.equiv (to_Modelnc isem ax) (to_Modelnc isem ax').
      Proof using.
        rewrite Model.equiv_weaker.
        rewrite equiv_weaker.
        intros [].
        split; by apply weaker_Model.
      Qed.
    End Ax.
  End Ax.

End CandidateExecutions.
