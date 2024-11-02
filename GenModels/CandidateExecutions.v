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
Require Import SSCCommon.StateT.

Require Import ISASem.Interface.
Require Import TermModels.

Open Scope Z_scope.
Open Scope stdpp_scope.

(* Module to be imported *)
Module CandidateExecutions (IWA : InterfaceWithArch) (Term : TermModelsT IWA).
  Import IWA.Arch.
  Import IWA.Interface.
  Import Term.

  #[local] Open Scope nat.

  Declare Scope eid_scope.
  #[local] Open Scope eid_scope.

  (** Relational event ID, this might differ from ISA events in certain
      execution types *)
  Module EID.
    Record t :=
      make {
          (** Thread ID, zero-indexed *)
          tid : nat;
          (** Instruction ID. The index of the instruction in program order  *)
          iid : nat;
          (** ISA event number in the instruction. Warning: this will stop being
              a [nat] when the interface monad supports parallel composition *)
          ieid : nat;
          (** Byte number for events that are split per byte, None for others *)
          byte : option N
          }.

    #[global] Instance eta : Settable _ :=
        settable! make <tid; iid; ieid; byte>.

    #[global] Instance cdestr_rec_inj : CDestrRecInj t make.
    Proof. Qed.

    #[global] Instance eq_dec : EqDecision t.
    Proof. solve_decision. Defined.


    #[global] Instance countable : Countable t.
    Proof.
      eapply (inj_countable' (fun eid => (tid eid, iid eid, ieid eid, byte eid))
                        (fun x => make x.1.1.1 x.1.1.2 x.1.2 x.2)).
      sauto.
    Qed.

    Definition po_lt (id1 id2 : t) : Prop :=
      id1.(tid) = id2.(tid) ∧ id1.(iid) < id2.(iid).

    Notation "x <ₚ y" := (po_lt x y) (at level 70, no associativity) : eid_scope.

    Definition iio_lt (id1 id2 : t) : Prop :=
      id1.(tid) = id2.(tid) ∧ id1.(iid) = id2.(iid) ∧ id1.(ieid) < id2.(ieid).

    Notation "x <ᵢ y" := (iio_lt x y) (at level 70, no associativity) : eid_scope.

    Definition full_po_lt (id1 id2 : t) : Prop :=
      id1 <ₚ id2 ∨ id1 <ᵢ id2.

    Notation "x <ₚ₊ᵢ y" := (full_po_lt x y) (at level 70, no associativity)
      : eid_scope.

  End EID.

  (* Namespace *)
  (* TODO rename to Cand ? *)
  Module Candidate.

    (** Type of execution and thus candidate. For now only Not-Mixed-Size and
        Mixed-size This determine how events are split in the [byte_per_event]
        function *)
    Inductive exec_type := NMS | MS.

    (** An ISA event is either represented by a single event in the candidate,
        or by an event per byte. This is the function that decides which event
        are split per byte. [None] means not split, and [Some n], means split in
        [n] *)
    Definition bytes_per_event (et : exec_type) (ev : iEvent) : list (option N) :=
      match et with
      | MS =>
          match ev with
          | MemRead n rr &→ _ =>
              let main := seqN 0 n |$> Some in
              if rr.(ReadReq.tag) then main else None :: main
          | _ => [None]
          end
      | NMS => [None]
      end.

    Lemma bytes_per_event_NoDup et ev : NoDup (bytes_per_event et ev).
    Proof. unfold bytes_per_event. solve_NoDup; set_solver. Qed.
    #[global] Hint Resolve bytes_per_event_NoDup : nodup.

    (** Gives the list of valid EIDs for a event at a specific position in a
        candidate *)
    Definition EID_list_from_iEvent (et : exec_type) (tid iid ieid : nat)
         (event : iEvent) : list EID.t :=
      EID.make tid iid ieid <$> bytes_per_event et event.

    Lemma EID_list_from_iEvent_NoDup et tid iid ieid ev :
      NoDup (EID_list_from_iEvent et tid iid ieid ev).
    Proof. unfold EID_list_from_iEvent. solve_NoDup. naive_solver. Qed.
    #[global] Hint Resolve EID_list_from_iEvent_NoDup : nodup.

    (** Converts a intra instruction nat relation over ieid into a relation over
        EID.t. Also require the trace of the instruction *)
    Definition convert_to_EID_rel (et : exec_type) (tid iid : nat)
      (ieid_rel : grel nat) (instr : iTrace ()) : grel EID.t :=
      ('(ieid1, ieid2) ← elements ieid_rel;
       iev1 ← option_list (instr.1 !! ieid1);
       iev2 ← option_list (instr.1 !! ieid2);
       (EID_list_from_iEvent et tid iid ieid1 iev1) ×
         (EID_list_from_iEvent et tid iid ieid2 iev2))
      |> list_to_set.

    Record pre {et : exec_type} {nmth : nat} :=
      make_pre {
          (** Initial state *)
          init : MState.t nmth;
          (** Each thread is a list of instruction who each have a trace,
              we force the return type to be unit, but it just means we
              forget the actual value *)
          events : vec (list (iTrace ())) nmth
        }.
    Arguments pre : clear implicits.
    Arguments make_pre _ {_}.

    #[global] Instance pre_eta {et nmth} : Settable (pre et nmth) :=
      settable! (@make_pre et nmth)
      <init; events>.

    Section Pre.
      Context {et : exec_type} {nmth : nat}.
      Implicit Type pe : (pre et nmth).

      (** Asserts that a candidate conforms to an ISA model.
        This version only supports ISA model without inter-instruction state.
        We'll see later if such state is required *)
      Definition ISA_match pe (isem : iMon ()) :=
        ∀ tid : fin nmth,
        ∀ trc ∈ pe.(events) !!! tid,
        cmatch isem trc.

      #[global] Instance ISA_match_dec pe isem : Decision (ISA_match pe isem).
      Proof using. unfold ISA_match. solve_decision. Qed.

      (** Asserts that all the trace in an execution are complete and not partial traces *)
      Definition ISA_complete pe :=
        ∀ thread ∈ (vec_to_list pe.(events)),
        ∀ instr ∈ thread,
        instr.2 = FTERet ().

      #[global] Instance ISA_complete_dec pe : Decision (ISA_complete pe).
      Proof using. unfold ISA_complete. tc_solve. Defined.

      (** This true if one of the instruction had an ISA model failure like a
          Sail assertion or an Isla assumption that failed. Due to out of order
          effects, an error might not be from the last instruction. *)
      Definition ISA_failed pe :=
        ∃ thread ∈ (vec_to_list pe.(events)),
        ∃ instr ∈ thread,
        ∃ msg, instr.2 = FTEStop (GenericFail msg).

      #[global] Instance ISA_failed_dec pe : Decision (ISA_failed pe).
      Proof using.
        unfold ISA_failed.
        apply list_exist_dec. intro.
        apply list_exist_dec. intro tr.
        destruct (tr.2) as [| | call]; try (right; abstract hauto lq:on).
        destruct call; (right + left); abstract hauto lq:on.
      Defined.

      Definition lookup_instruction pe (tid iid : nat) :
          option (iTrace ()) :=
        traces ← pe.(events) !! tid;
        traces !! iid.

      Definition instruction_list pe : list (nat * nat * iTrace ()) :=
        '(tid, traces) ← enumerate pe.(events);
        '(iid, trace) ← enumerate traces;
        [(tid, iid, (trace : iTrace ()))].


      (** Allow [set_unfold] to unfold through [match] constructs *)
      #[local] Existing Instance set_unfold_match.

      Lemma instruction_list_match pe tid iid ev :
        lookup_instruction pe tid iid = Some ev ↔
          (tid, iid, ev) ∈ instruction_list pe.
      Proof using.
        destruct ev.
        unfold lookup_instruction.
        unfold instruction_list.
        set_unfold.
        setoid_rewrite lookup_unfold.
        setoid_rewrite eq_some_unfold.
        repeat setoid_rewrite exists_pair.
        naive_solver.
      Qed.
      Global Typeclasses Opaque lookup_instruction.
      Opaque lookup_instruction.
      Global Typeclasses Opaque instruction_list.

      Definition lookup_iEvent pe (tid iid ieid : nat) :
        option iEvent :=
      '(trace, result) ← lookup_instruction pe tid iid;
      trace !! ieid.

      Definition iEvent_list pe : list (nat * nat * nat * iEvent) :=
        '(tid, iid, (trace, trace_end)) ← instruction_list pe;
        '(ieid, event) ← enumerate trace;
        mret (tid, iid, ieid, event).

      Lemma iEvent_list_match pe tid iid ieid ev :
        lookup_iEvent pe tid iid ieid = Some ev ↔
          (tid, iid, ieid, ev) ∈ iEvent_list pe.
      Proof using.
        unfold lookup_iEvent.
        unfold iEvent_list.
        set_unfold.
        setoid_rewrite eq_some_unfold.
        setoid_rewrite instruction_list_match.
        repeat setoid_rewrite exists_pair.
        set_solver.
      Qed.
      #[global] Typeclasses Opaque lookup_iEvent.
      Opaque lookup_iEvent.
      #[global] Typeclasses Opaque iEvent_list.

      Definition EID_list_from_event_ids pe (tid iid ieid : nat) :
          list EID.t :=
        ev ← option_list (lookup_iEvent pe tid iid ieid);
        EID_list_from_iEvent et tid iid ieid ev.

      (** Get an event at a given event ID in a pre-execution *)
      Global Instance lookup_eid_pre : Lookup EID.t iEvent (pre et nmth) :=
        λ eid pe,
          ev ← lookup_iEvent pe eid.(EID.tid) eid.(EID.iid) eid.(EID.ieid);
          guard (eid.(EID.byte) ∈ bytes_per_event et ev);;
          Some ev.
      #[global] Typeclasses Opaque lookup_eid_pre.

      Definition event_list pe : list (EID.t * iEvent) :=
        '(tid, iid, ieid, event) ← iEvent_list pe;
        EID_list_from_iEvent et tid iid ieid event |$> (.,event).
      Global Typeclasses Opaque event_list.

      Lemma event_list_match pe eid ev :
        pe !! eid = Some ev ↔ (eid, ev) ∈ event_list pe.
      Proof using.
        unfold lookup at 1.
        unfold lookup_eid_pre.
        unfold event_list.
        unfold EID_list_from_iEvent.
        destruct eid.
        set_unfold.
        setoid_rewrite eq_some_unfold.
        setoid_rewrite iEvent_list_match.
        repeat setoid_rewrite exists_pair.
        naive_solver.
      Qed.

      Global Instance set_unfold_elem_of_event_list pe x :
        SetUnfoldElemOf x (event_list pe) (pe !! x.1 = Some x.2).
      Proof using . tcclean. destruct x. symmetry. apply event_list_match. Qed.

      (* Hint Constants Transparent : typeclass_instances. *)
      (* Typeclasses Opaque elem_of. *)
      Lemma event_list_NoDup1 pe : NoDup (event_list pe).*1.
      Proof using.
        unfold event_list.
        unfold iEvent_list.
        unfold instruction_list.
        unfold EID_list_from_iEvent.
        rewrite fmap_unfold #FMapUnfoldFmap.
        solve_NoDup; set_unfold; cdestruct |- **; congruence.
      Qed.

      Lemma event_list_NoDup pe : NoDup (event_list pe).
      Proof using. eapply NoDup_fmap_1. apply event_list_NoDup1. Qed.

      Definition event_map pe : gmap EID.t iEvent :=
        event_list pe |> list_to_map.

      Lemma event_map_match pe eid : (event_map pe) !! eid = pe !! eid.
      Proof using.
        unfold event_map.
        destruct (pe !! eid) eqn: Heq.
        - apply elem_of_list_to_map.
          + apply event_list_NoDup1.
          + set_solver.
        - apply not_elem_of_list_to_map_1.
          set_solver.
      Qed.

      Global Instance lookup_unfold_event_map x pe R :
        LookupUnfold x pe R → LookupUnfold x (event_map pe) R.
      Proof using. tcclean. apply event_map_match. Qed.

      (** * Accessors ***)

      Definition collect_all (P : EID.t -> iEvent -> Prop)
        `{∀ eid event, Decision (P eid event)}
        pe : gset EID.t :=
        filter (fun '(eid, event) => P eid event) (event_list pe)
          |> map fst |> list_to_set.
      Global Instance set_elem_of_collect_all eid P
        `{∀ eid event, Decision (P eid event)} pe :
        SetUnfoldElemOf eid (collect_all P pe) (∃x, pe !! eid = Some x ∧ P eid x).
      Proof using. tcclean. unfold collect_all. set_unfold. hauto db:pair. Qed.
      Global Typeclasses Opaque collect_all.

      (** Get the set of all valid EID for that candidate *)
      Definition valid_eids pe :=
        collect_all (fun _ _ => True) pe.

      Global Instance set_elem_of_valid_eids eid pe :
        SetUnfoldElemOf eid (valid_eids pe) (is_Some (pe !! eid)).
      Proof using. tcclean. unfold valid_eids. set_unfold. hauto db:pair. Qed.
      Global Typeclasses Opaque valid_eids.

      (** Get the set of all register reads *)
      Definition reg_reads := collect_all (λ _, is_reg_read).
      Definition pc_reads :=
        collect_all (λ _, is_reg_readP (λ reg _ _, reg = pc_reg)).

      (** Get the set of all register writes *)
      Definition reg_writes := collect_all (λ _, is_reg_write).
      Definition pc_writes :=
        collect_all (λ _, is_reg_writeP (λ reg _ _, reg = pc_reg)).

      (** Get the set of all memory reads *)
      Definition mem_reads := collect_all (λ _, is_mem_read).
      Typeclasses Opaque mem_reads.
      Definition mem_read_reqs:= collect_all (λ _ , is_mem_read_req).
      Typeclasses Opaque mem_read_reqs.
      Definition mem_read_aborts :=
        collect_all (λ _, is_mem_read_reqP (λ _ _, is_inr)).
      Typeclasses Opaque mem_read_aborts.

      Lemma mem_read_reqs_union pe :
        mem_read_reqs pe = mem_reads pe ∪ mem_read_aborts pe.
      Proof.
        unfold mem_reads, mem_read_reqs, mem_read_aborts.
        set_unfold.
        split;
          cdestruct |- ** ##cdestruct_or ##cdestruct_sum;
          naive_solver.
      Qed.

      (** Get the set of all memory writes *)
      Definition mem_write_addr_announces := collect_all (λ _, is_mem_write_addr_announce).
      Typeclasses Opaque mem_write_addr_announces.
      Definition mem_writes := collect_all (λ _, is_mem_write).
      Typeclasses Opaque mem_writes.
      Definition mem_write_reqs := collect_all (λ _, is_mem_write_req).
      Typeclasses Opaque mem_write_reqs.
      Definition mem_write_aborts :=
        collect_all (λ _, is_mem_write_reqP (λ _ _ res, res ≠ inl true)).
      Typeclasses Opaque mem_write_aborts.

      Lemma mem_write_reqs_union pe :
        mem_write_reqs pe = mem_writes pe ∪ mem_write_aborts pe.
      Proof.
        unfold mem_writes, mem_write_reqs, mem_write_aborts.
        set_unfold.
        split;
          cdestruct |- ** ##cdestruct_or ##cdestruct_sum # (CDestrCase bool);
          naive_solver.
      Qed.

      Definition mem_events := collect_all (λ _, is_mem_event).
      Typeclasses Opaque mem_events.

      Lemma mem_events_union pe : mem_events pe = mem_reads pe ∪ mem_writes pe.
      Proof. unfold mem_events, mem_reads, mem_writes, is_mem_event. set_solver. Qed.

      (* WARNING: intense boilerplate *)
      Section ByKind.
        Context (P : accessKind → Prop).
        Context {Pdec : ∀ acc, Decision (P acc)}.
        Definition mem_by_kind := collect_all (λ _, is_mem_event_kindP P).
        #[global] Typeclasses Opaque mem_by_kind.
        Definition reads_by_kind := collect_all (λ _, is_mem_read_kindP P).
        #[global] Typeclasses Opaque reads_by_kind.
        Definition writes_by_kind := collect_all (λ _, is_mem_write_kindP P).
        #[global] Typeclasses Opaque writes_by_kind.
      End ByKind.
      Definition mem_explicit := (mem_by_kind is_explicit).
      Definition explicit_reads := (reads_by_kind is_explicit).
      Definition explicit_writes := (writes_by_kind is_explicit).
      Definition mem_ifetch := (mem_by_kind is_ifetch).
      Definition ifetch_reads := (reads_by_kind is_ifetch).
      Definition ifetch_writes := (writes_by_kind is_ifetch). (* empty *)
      Definition mem_ttw := (mem_by_kind is_ttw).
      Definition ttw_reads := (reads_by_kind is_ttw).
      Definition ttw_writes := (writes_by_kind is_ttw).
      Definition mem_relaxed := (mem_by_kind is_relaxed).
      Definition relaxed_reads := (reads_by_kind is_relaxed).
      Definition relaxed_writes := (writes_by_kind is_relaxed).
      Definition mem_rel_acq := (mem_by_kind is_rel_acq).
      Definition rel_acq_reads := (reads_by_kind is_rel_acq).
      Definition rel_acq_writes := (writes_by_kind is_rel_acq).
      Definition mem_acq_rcpc := (mem_by_kind is_acq_rcpc).
      Definition acq_rcpc_reads := (reads_by_kind is_acq_rcpc).
      Definition acq_rcpc_writes := (writes_by_kind is_acq_rcpc).
      Definition mem_standalone := (mem_by_kind is_standalone).
      Definition standalone_reads := (reads_by_kind is_standalone).
      Definition standalone_writes := (writes_by_kind is_standalone).
      Definition mem_exclusive := (mem_by_kind is_exclusive).
      Definition exclusive_reads := (reads_by_kind is_exclusive).
      Definition exclusive_writes := (writes_by_kind is_exclusive).
      Definition mem_atomic_rmw := (mem_by_kind is_atomic_rmw).
      Definition atomic_rmw_reads := (reads_by_kind is_atomic_rmw).
      Definition atomic_rmw_writes := (writes_by_kind is_atomic_rmw).

      (** Get the set of all barriers *)
      Definition barriers pe :=
        collect_all (λ _ event, is_Some (get_barrier event)) pe.
      Typeclasses Opaque barriers.

      (** Get the set of all cache operations *)
      Definition cacheops pe :=
        collect_all (λ _ event, is_Some (get_cacheop event)) pe.
      Typeclasses Opaque cacheops.

      (** Get the set of all TLB operations *)
      Definition tlbops pe :=
        collect_all (λ _ event, is_Some (get_tlbop event)) pe.
      Typeclasses Opaque tlbops.


      (** * Supported events

        This framework does not support all kind of events yet. It does not support:
        - memory tags
        - Rejecting exclusive memory writes *)
      Definition unsupported_event (ev : iEvent) : Prop :=
        is_mem_read_reqP (λ n rr _, rr.(ReadReq.tag)) ev ∨
        is_mem_write_reqP (λ n wr r, is_Some (wr.(WriteReq.tag))) ev.
      #[global] Typeclasses Transparent unsupported_event.

      Definition has_only_supported_events pe : Prop :=
        iEvent_list pe |> filter (λ '(_,ev), unsupported_event ev) = [].

          (** Get the final register maps of all threads from a candidate *)
      Definition final_reg_map_tid pe (tid : fin nmth) :
          registerMap :=
        λ reg,
        let oval :=
          foldl (λ val itrc,
              foldl (λ (val : option (reg_type reg)) ev,
                  match ev with
                  | RegWrite reg' _ val' &→ _ =>
                      if decide (reg' = reg) is left e
                      then Some (ctrans e val')
                      else val
                  | _ => val
                  end
                ) val itrc.1
            ) None (pe.(events) !!! tid)
        in
        if oval is Some val then val else (pe.(init).(MState.regs) !!! tid) reg.

      (** Get all the final register map from candidate *)
      Definition final_reg_map pe : vec registerMap nmth :=
        fun_to_vec (final_reg_map_tid pe).

      (** * Utility relations **)


      (** ** Relation building helpers *)

      (** This helper computes an optional key from each eid and event pair of a
          candidate using [get_key], and gathers all eids with the same key
          together into a set. It returns a map from keys to sets of eids *)
      Definition gather_by_key `{Countable K} pe
          (get_key : EID.t -> iEvent -> option K) : gmap K (gset EID.t) :=
        fold_left (λ acc '(eid, event), match get_key eid event with
                                        | Some k => {[ k := {[eid]}]}
                                        | None => ∅
                                        end ∪ₘ acc) (event_list pe) ∅.
      #[global] Typeclasses Opaque gather_by_key.

      Global Instance set_elem_of_gather_by_key_lookup `{Countable K} pe
        (get_key : EID.t → iEvent → option K) (k: K) (eid : EID.t):
        SetUnfoldElemOf eid (gather_by_key pe get_key !!! k)
          (∃ E, pe !! eid = Some E ∧ get_key eid E = Some k).
      Proof.
        tcclean.
        unfold gather_by_key.
        orewrite* (fold_left_inv_ND
          (λ map tl, ∀ eid k,
            eid ∈ map !!! k ↔
              ∃ ev, pe !! eid = Some ev
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

      Global Instance lookup_total_unfold_gather_by_key `{Countable K} pe
          (get_key : EID.t → iEvent → option K) (k: K):
        LookupTotalUnfold k (gather_by_key pe get_key)
          (collect_all (λ eid event, get_key eid event = Some k) pe).
      Proof. tcclean. set_solver. Qed.


      Lemma gather_by_key_None `{Countable K} pe
          (get_key : EID.t → iEvent → option K) (k : K):
        gather_by_key pe get_key !! k = None ↔
        ∀ eid ev, (eid, ev) ∈ event_list pe → get_key eid ev ≠ Some k.
      Proof.
        unfold gather_by_key.
        orewrite* (fold_left_inv_ND
          (λ map tl, ∀ k,
            map !! k = None ↔
              ∀ eid ev, (eid, ev) ∈ event_list pe →
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
      Lemma lookup_is_Some_gather_by_key `{Countable K} pe
          (get_key : EID.t → iEvent → option K) (k: K):
        (∃ eid event, (eid, event) ∈ event_list pe ∧ get_key eid event = Some k) →
        is_Some (gather_by_key pe get_key !! k).
      Proof.
        destruct (gather_by_key pe get_key !! k) eqn:Heqn.
        - done.
        - rewrite gather_by_key_None in Heqn.
          naive_solver.
      Qed.

      (** Returns an equivalence relation, such that two events are in the relation
          iff they have the same key computed with [get_key] *)
      Definition same_key `{Countable K} (get_key : EID.t -> iEvent -> option K)
          pe :=
        finmap_reduce_union (λ k s, s × s) (gather_by_key pe get_key).

      (** An unfold instance for [same_key] *)
      Global Instance set_elem_of_same_key `{Countable K} pe
        get_key eids :
        SetUnfoldElemOf eids
          (same_key get_key pe)
          (∃ E1 E2 (k: K), pe !! eids.1 = Some E1 ∧ pe !! eids.2 = Some E2
                          ∧ get_key eids.1 E1 = Some k ∧ get_key eids.2 E2 = Some k).
      Proof.
        tcclean. destruct eids. unfold same_key.
        set_unfold.
        split.
        - intros (?&?&?&?).
          lookup_lookup_total; set_solver.
        - intros (?&?&k&?). destruct_and!.
          opose proof* (lookup_is_Some_gather_by_key pe get_key k) as [? HSome].
          { set_solver. }
          do 2 eexists.
          repeat split_and; first eassumption.
          all: lookup_lookup_total; set_solver.
      Qed.
      #[global] Typeclasses Opaque same_key.


      (** ** Thread and instruction based orders and relations *)

      Class UnfoldEidRels := {}.
      #[local] Instance unfold_eid_rels : UnfoldEidRels := ltac:(constructor).

      (** Equivalence relation relating events from the same thread *)
      Definition same_thread : (pre et nmth) → grel EID.t :=
        same_key (λ eid _, Some (eid.(EID.tid))).
      #[global] Typeclasses Opaque same_thread.
      #[global] Instance set_elem_of_same_thread `{UnfoldEidRels} pe eids:
        SetUnfoldElemOf eids (same_thread pe)
          (is_Some (pe !! eids.1) ∧ is_Some (pe !! eids.2) ∧
            eids.1.(EID.tid) = eids.2.(EID.tid)).
      Proof.
        tcclean.
        destruct eids.
        unfold same_thread.
        set_unfold.
        hauto q:on.
      Qed.

      (** Equivalence relation relating events from the same instruction instance *)
      Definition same_instruction_instance : (pre et nmth) → grel EID.t :=
        same_key (λ eid _, Some (eid.(EID.tid), eid.(EID.iid))).
      #[global] Typeclasses Opaque same_instruction_instance.
      #[global] Instance set_elem_of_same_instruction_instance `{UnfoldEidRels} pe eids:
        SetUnfoldElemOf eids (same_instruction_instance pe)
          (is_Some (pe !! eids.1) ∧ is_Some (pe !! eids.2) ∧
            eids.1.(EID.tid) = eids.2.(EID.tid) ∧
            eids.1.(EID.iid) = eids.2.(EID.iid)).
      Proof.
        tcclean.
        destruct eids.
        unfold same_instruction_instance.
        set_unfold.
        hauto q:on.
      Qed.

      (** Equivalence relation relating bytes event from the same memory access *)
      Definition same_access : (pre et nmth) → grel EID.t :=
        same_key
          (λ eid _, Some (eid.(EID.tid), eid.(EID.iid), eid.(EID.ieid))).
      #[global] Typeclasses Opaque same_access.
      #[global] Instance set_elem_of_same_access `{UnfoldEidRels} pe eids:
        SetUnfoldElemOf eids (same_access pe)
          (is_Some (pe !! eids.1) ∧ is_Some (pe !! eids.2) ∧
            eids.1.(EID.tid) = eids.2.(EID.tid) ∧
            eids.1.(EID.iid) = eids.2.(EID.iid) ∧
            eids.1.(EID.ieid) = eids.2.(EID.ieid)).
      Proof.
        tcclean.
        destruct eids.
        unfold same_access.
        set_unfold.
        hauto q:on.
      Qed.

      (** Intra Instruction Order: The order in which events ran inside an
          instruction

          This is intended to disappear in future versions,
          try not to depend on it *)
      Definition iio pe :=
        same_instruction_instance pe
        |> filter (λ eids, eids.1.(EID.ieid) < eids.2.(EID.ieid)).
      #[global] Typeclasses Opaque iio.
      #[global] Instance set_elem_of_iio`{UnfoldEidRels} pe eids:
      SetUnfoldElemOf eids (iio pe)
        (is_Some (pe !! eids.1) ∧ is_Some (pe !! eids.2) ∧
          eids.1.(EID.tid) = eids.2.(EID.tid) ∧
          eids.1.(EID.iid) = eids.2.(EID.iid) ∧
          eids.1.(EID.ieid) < eids.2.(EID.ieid)). (* Should use <ᵢ *)
      Proof.
        tcclean.
        destruct eids.
        unfold iio.
        set_unfold.
        naive_solver lia.
      Qed.

      (** Order in which the instructions architecturally ran. This does not mean
          they micro-architecturally run in that specific order. This is an inter
          instruction order, it does not order the events inside an instructions
          (see [iio] for that) *)
      Definition instruction_order pe :=
        same_thread pe
        |> filter (λ eids, eids.1.(EID.iid) < eids.2.(EID.iid)).
      #[global] Typeclasses Opaque instruction_order.
      #[global] Instance set_elem_of_instruction_order`{UnfoldEidRels} pe eids:
      SetUnfoldElemOf eids (instruction_order pe)
        (is_Some (pe !! eids.1) ∧ is_Some (pe !! eids.2) ∧
          eids.1.(EID.tid) = eids.2.(EID.tid) ∧
          eids.1.(EID.iid) < eids.2.(EID.iid)).
      Proof.
        tcclean.
        destruct eids.
        unfold instruction_order.
        set_unfold.
        naive_solver lia.
      Qed.

      (** Complete thread order. This is a strict partial order on each thread
          events denoting event that happened sequentially before other according
          to the program and instruction semantics. This does NOT means that this
          order implies any kind of weak memory ordering *)
      Definition full_instruction_order pe := instruction_order pe ∪ iio pe.

      (** ** Memory based relations *)

      Implicit Type ev : iEvent.

      (** Equivalence relation relating memory events that have the same physical
          address. In an [MixedSize] model which splits reads but not write, this
          is based on the pa of the whole read *)
      Definition same_pa : (pre et nmth) → grel EID.t :=
        same_key (λ _, get_pa).
      Typeclasses Opaque same_pa.

      Definition get_pa_footprint (eid : EID.t) ev : option (pa * N) :=
        pa ← get_pa ev;
        match eid.(EID.byte) with
        | None => get_size ev |$> (pa,.)
        | Some n => Some (pa_addN pa n, 1%N)
        end.
      Typeclasses Opaque get_pa_footprint.

      (** Equivalence relation relating memory events that have the same size. *)
      Definition same_size : (pre et nmth) → grel EID.t :=
        same_key (λ _, get_size).
      Typeclasses Opaque same_size.

      Definition same_footprint pe := same_pa pe ∩ same_size pe.

      (** Equivalence relation relating memory event that have the same size and value *)
      Definition same_mem_value : (pre et nmth) → grel EID.t :=
        same_key (λ _, get_mem_value).
      Typeclasses Opaque same_mem_value.

      Lemma same_mem_value_size pe :
        same_mem_value pe ⊆ same_size pe.
      Proof.
        unfold same_mem_value,same_size.
        set_unfold.
        hauto lq:on rew:off use:get_mem_value_size.
      Qed.

      (** Decide if two memory event are overlapping. False is either of them is
      not a memory event *)
      Definition is_overlapping pe (eid1 eid2 : EID.t) : Prop :=
        is_Some $
          e1 ← pe !! eid1;
          '(pa1, size1) ← get_pa_footprint eid1 e1;
          e2 ← pe !! eid2;
          '(pa2, size2) ← get_pa_footprint eid2 e2;
          guard' (pa_overlap pa1 size1 pa2 size2).

      #[global] Instance is_overlapping_dec pa eid1 eid2 : Decision (is_overlapping pa eid1 eid2).
      Proof. unfold is_overlapping. tc_solve. Qed.

      Lemma is_overlapping_sym pe eid1 eid2 :
        is_overlapping pe eid1 eid2 → is_overlapping pe eid2 eid1.
      Proof.
        unfold is_overlapping, is_Some in *.
        cdestruct |- ? # CDestrEqSome.
        typeclasses eauto with core pa option.
      Qed.

      Lemma is_overlapping_sym_iff pe eid1 eid2 :
        is_overlapping pe eid1 eid2 ↔ is_overlapping pe eid2 eid1.
      Proof. split; apply is_overlapping_sym. Qed.

      (** Relates overlapping memory event *)
      Definition overlapping pe :=
        mem_events pe × mem_events pe
        |> filter (λ '(eid1, eid2), is_overlapping pe eid1 eid2).
      #[global] Typeclasses Transparent overlapping.

      Lemma overlapping_sym pe : grel_symmetric (overlapping pe).
      Proof.
        rewrite grel_symmetric_spec.
        use is_overlapping_sym.
        set_unfold.
        set_solver.
      Qed.

      (** Decide if a pre-execution does not involve mixed size accesses *)
      Definition is_nms pe := overlapping pe ⊆ same_footprint pe.

      (** ** Register based relations *)

      (** Equivalence relation relating register events referring to the same
      register *)
      Definition same_reg : (pre et nmth) →  grel EID.t :=
        same_key (λ eid ev, get_reg ev |$> (EID.tid eid,.)).
      Typeclasses Opaque same_reg.

      (** Equivalence relation relating register events refering to the same
      register with the same value *)
      Definition same_reg_val : (pre et nmth) →  grel EID.t :=
        same_key (λ eid ev, get_reg_val ev |$> (EID.tid eid,.)).
      Typeclasses Opaque same_reg_val.

      Lemma same_reg_val_same_reg pe :
        same_reg_val pe ⊆ same_reg pe.
      Proof.
        unfold same_reg,same_reg_val.
        set_unfold.
        cdestruct |- ** #CDestrEqSome.
        setoid_rewrite eq_some_unfold.
        hauto lq:on rew:off use:get_reg_val_get_reg.
      Qed.

      Definition is_valid_init_reg_read pe (eid : EID.t) : iEvent → Prop :=
        is_reg_readP (λ reg _ rv,
            match pe.(init).(MState.regs) !! eid.(EID.tid) with
            | Some regmap => rv = regmap reg
            | None => False
            end).
      #[global] Instance is_valid_init_reg_read_dec pe eid ev :
        Decision (is_valid_init_reg_read pe eid ev).
      Proof. unfold is_valid_init_reg_read. tc_solve. Defined.

      Definition is_valid_init_reg_read_spec pe (eid : EID.t) (ev : iEvent):
        is_valid_init_reg_read pe eid ev ↔
          ∃ reg reg_acc rv,
            (ev = RegRead reg reg_acc &→ rv) ∧
              ∃ H : eid.(EID.tid) < nmth,
                (pe.(init).(MState.regs) !!! nat_to_fin H) reg = rv.
      Proof.
        unfold is_valid_init_reg_read.
        split; cdestruct ev |- ** #CDestrMatch #CDestrEqSome.
        - naive_solver.
        - cbn. by erewrite vec_lookup_nat_in.
      Qed.
      Definition is_valid_init_reg_read_cdestr pe eid ev :=
        cdestr_simpl (is_valid_init_reg_read_spec pe eid ev).
      #[global] Existing Instance is_valid_init_reg_read_cdestr.

      Definition possible_initial_reg_reads pe :=
        collect_all (is_valid_init_reg_read pe) pe.
      #[global] Typeclasses Opaque possible_initial_reg_reads.

      Lemma possible_initial_reg_reads_ok pe :
        possible_initial_reg_reads pe ⊆ reg_reads pe.
      Proof.
        unfold possible_initial_reg_reads, reg_reads.
        set_unfold.
        cdestruct |- **.
        naive_solver.
      Qed.

      Definition is_valid_init_mem_read pe (eid : EID.t) :=
        is_Some $
        read ← pe !! eid;
        guard (is_mem_read read);;
        pa ← get_pa read;
        val ← get_mem_value read;
        guard' (val = memoryMap_read pe.(init).(MState.memory) pa (bvn_n val / 8)).

    End Pre.

    (** A candidate execution. It consists of a pre-execution defined by init +
        events, and set of relation describing what happened in the execution.
        In order to be called an "execution" it must be valid according to three
        criteria:
        - It must match with the ISA model (instruction by instruction).
          See [ISA_match]
        - It must be well formed (which depends on the [exec_type]).
          See [TODO]
        - It must be valid according to some model. See [Ax]. *)
    Record t {et : exec_type} {nmth : nat} :=
      make {
          (** The preexecution this candidate is based on *)
          pre_exec :> pre et nmth;
          (** Relate a memory read with the write it gets it's value from *)
          reads_from : grel EID.t;
          (** Register read from (needed because of potentially relaxed
              register). For non-relaxed register, this must link a register
              read to the nearest po-previous write. *)
          reg_reads_from : grel EID.t;
          (** Generic coherence order for all events that affect shared machine
              state like memory (but not only). For now this includes:
              - memory writes
              - Cache and TLB operations
              In theory this could be a total order but most memory models relax
              this requirement for writes that don't overlap. Other than that
              there is a bit of leeway on how strict or lax this relation is,
              which up for individual models to decide. For reference what
              should go in this relation is basically the same as what should go
              a promising model "memory" trace *)
          coherence : grel EID.t;
          (** Load-reserve/store conditional pair (exclusives in Arm speak) *)
          lxsx : grel EID.t
        }.
    Arguments t : clear implicits.
    Arguments make _ {_}.

    #[global] Instance eta {et nmth} : Settable (t et nmth) :=
        settable! (@make et nmth)
        <pre_exec; reads_from; reg_reads_from; coherence; lxsx>.

    (** Notations to mean init and events on [t] and not [pre]. Useful for
        setting, not for getting where coercion inference is good enough. *)
    Notation init' := (init : t _ _ → _).
    Notation events' := (events : t _ _ → _).

    Section Cand.
    Context {et : exec_type} {nmth : nat}.
    Notation t := (t et nmth).
    Implicit Type cd : t.

    (** Get an event at a given event ID in a pre-execution *)
    Global Instance lookup_eid_candidate : Lookup EID.t iEvent t :=
      λ eid cd, (pre_exec cd) !! eid.
    #[global] Typeclasses Opaque lookup_eid_candidate.

    (** * Connection to final state *)

    (** Get the list of final register values in a candidate for a thread *)
    (* TODO fix it when Dmaps are working *)
    (* Definition final_reg_gmap_tid (cd : t) (tid : fin nmth) : *)
    (*   gmap reg reg_type := *)
    (*   foldl (λ umap itrc, *)
    (*       foldl (λ umap ev, *)
    (*           match ev with *)
    (*           | RegWrite reg _ val &→ _ => <[reg := val]> umap *)
    (*           | _ => umap *)
    (*           end *)
    (*         ) umap itrc.1 *)
    (*     ) (∅ : gmap reg reg_type) (cd.(events) !!! tid). *)


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
                      match decide ((eid, eid') ∈ cd.(coherence)) with
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


    (** ** Memory based relations *)


    (** The set of initial memory reads *)
    Definition init_mem_reads cd :=
      mem_reads cd ∖ grel_rng (reads_from cd).
    #[global] Typeclasses Opaque init_mem_reads.

    (** The definition of [from_reads] is a bit unusual, because initial
        memory/initial writes are not represented as events. A write event is
        after a read event it the footprints overlap and the write event is not
        before the read event (aka the read reads from the write, or a
        coherence-later write)*)
    Definition from_reads cd :=
      (⦗mem_reads cd⦘⨾ overlapping cd ⨾⦗mem_writes cd⦘)
        ∖ ((coherence cd ∪ ⦗reg_writes cd⦘) ⨾ reads_from cd)⁻¹.
    #[global] Typeclasses Opaque from_reads.



    (** ** Register based relations *)


    (** The set of initial register reads *)
    Definition initial_reg_reads cd :=
      reg_reads cd ∖ grel_rng (reg_reads_from cd).
    #[global] Typeclasses Opaque initial_reg_reads.

    (** Orders a register write after a read that read a po-earlier write. This
        might run against the instruction order for relaxed registers but follow the
        instruction order for regular register *)
    Definition reg_from_reads cd :=
      ⦗reg_reads cd⦘⨾ same_reg cd ⨾⦗reg_writes cd⦘
        ∖ ((instruction_order cd ∪ ⦗reg_writes cd⦘)⨾ reg_reads_from cd)⁻¹.
    #[global] Typeclasses Opaque reg_from_reads.

    Definition pc_reads_from cd := ⦗pc_writes cd⦘⨾ reg_reads_from cd ⨾⦗pc_reads cd⦘.
    Definition reg_reads_from_data cd := reg_reads_from cd ∖ pc_reads_from cd.

    (** * Generic wellformedness
        This section is for wellformedness properties that are not dependent on
        the execution type [et] *)

    (** *** Reads from wellformedness *)

    Definition is_valid_rf (cd : t) (weid reid : EID.t) : Prop :=
      is_Some $
      write ← cd !! weid;
      wpa ← get_pa write;
      wval ← get_mem_value write;
      read ← cd !! reid;
      rpa ← get_pa read;
      rval ← get_mem_value read;
      match reid.(EID.byte) with
      | Some n =>
          let rpa' := pa_addN rpa n in
          rbyte ← (bv_to_bytes 8 (bvn_val rval)) !! n;
          offset ← pa_diffN rpa' wpa;
          wbyte ← (bv_to_bytes 8 (bvn_val wval)) !! offset;
          guard' (rbyte = wbyte)
      | None =>
          guard' (rpa = wpa ∧ wval = rval)
          (* wval and rval are dynamic sized bitvector, so this also checks
             that both accesses are the same size *)
      end.



    Record reads_from_wf {cd : t} :=
      {
        rf_from_writes: grel_dom (reads_from cd) ⊆ (mem_writes cd);
        rf_to_reads: grel_rng (reads_from cd) ⊆ (mem_reads cd);
        rf_functional: grel_functional (reads_from cd)⁻¹;
        rf_valid: ∀'(weid, reid) ∈ reads_from cd, is_valid_rf cd weid reid;
        rf_valid_initial:
        ∀ reid ∈ init_mem_reads cd, is_valid_init_mem_read cd reid
      }.
    #[global] Arguments reads_from_wf : clear implicits.


    (** *** Coherence wellformedness *)


    Record coherence_wf {cd : t} :=
      {
        co_transitive : grel_transitive (coherence cd);
        co_irreflexive: grel_irreflexive (coherence cd);
        co_contains_overlapping_writes:
        ∀ weid1 weid2 ∈ mem_writes cd,
          is_overlapping cd weid1 weid2 →
          (weid1, weid2) ∈ coherence cd ∨ (weid2, weid1) ∈ coherence cd
      }.
    #[global] Arguments coherence_wf : clear implicits.

    (** *** lxsx wellformedness *)

    Record lxsx_wf {cd : t} :=
      {
        lxsx_from_reads : grel_dom (lxsx cd) ⊆ mem_reads cd ∩ mem_exclusive cd;
        lxsx_to_writes : grel_rng (lxsx cd) ⊆ mem_writes cd ∩ mem_exclusive cd;
        lxsx_instruction_order : lxsx cd ⊆ instruction_order cd;
        lxsx_same_pa : lxsx cd ⊆ same_pa cd
      }.
    #[global] Arguments lxsx_wf : clear implicits.


    (** *** Reg reads from wellformedness

        Standard wellformedness condition for reg_reads_from (or rrf in short).
        This does not relate register accesses to thread order. In particular,
        in this definition, a register read can read from any register write in
        the same thread either before or after in the thread order. *)
    Record reg_reads_from_wf {cd : t} :=
      {
        rrf_from_writes: grel_dom (reg_reads_from cd) ⊆ (reg_writes cd);
        rrf_to_reads: grel_rng (reg_reads_from cd) ⊆ (reg_reads cd);
        rrf_functional: grel_functional (reg_reads_from cd)⁻¹;
        rrf_same_reg_val: reg_reads_from cd ⊆ same_reg_val cd;
        rrf_initial_valid:
          initial_reg_reads cd ⊆ possible_initial_reg_reads cd;
      }.
    #[global] Arguments reg_reads_from_wf : clear implicits.

    Lemma rrf_irreflexive (cd : t) :
      reg_reads_from_wf cd → grel_irreflexive (reg_reads_from cd).
    Proof.
      intros [].
      unfold grel_irreflexive.
      intros eid H.
      assert (eid ∈ reg_writes cd) as Hw by set_solver.
      assert (eid ∈ reg_reads cd) as Hr by set_solver.
      unfold reg_reads, reg_writes in Hr, Hw.
      set_unfold.
      cdestruct Hw, Hr.
      congruence.
    Qed.

    Lemma rrf_same_reg (cd : t) :
      reg_reads_from_wf cd → reg_reads_from cd ⊆ same_reg cd.
    Proof. intros []. set_solver ##(@same_reg_val_same_reg et). Qed.

    Lemma rrf_reg_reads_decomp (cd : t) :
      reg_reads_from_wf cd →
      reg_reads cd = initial_reg_reads cd ∪ grel_rng (reg_reads_from cd).
    Proof.
      intros [].
      unfold initial_reg_reads.
      rewrite difference_union_L.
      set_solver.
    Qed.

    (** ** Full wellformedness *)

    Record wf (cd : t) :=
      {
        has_only_supported_events' :> has_only_supported_events cd;
        reads_from_wf' :> reads_from_wf cd;
        coherence_wf' :> coherence_wf cd;
        lxsx_wf' :> lxsx_wf cd;
        reg_reads_from_wf' :> reg_reads_from_wf cd;
      }.
    End Cand.

    (** * Dependency relations *)

    Section Deps.
      Context {et n} (cd : t et n).

      Definition iio_addr :=
          iio cd ⨾
            ((⦗mem_write_addr_announces cd⦘⨾ iio cd⨾ ⦗mem_write_reqs cd⦘ ∩
               same_footprint cd) ∪ ⦗mem_reads cd⦘).

      (* TODO prove wellformedness properties from the definition *)
      Definition addr :=
        ⦗mem_reads cd⦘⨾
          (⦗mem_reads cd⦘ ∪ (iio cd ⨾ reg_reads_from_data cd)⁺)⨾
          iio_addr⨾
          ⦗mem_events cd⦘.
      Global Typeclasses Opaque addr.

      Definition data :=
        ⦗mem_reads cd⦘⨾
          (⦗mem_reads cd⦘ ∪ (iio cd ⨾ (reg_reads_from_data cd))⁺)⨾
          iio cd⨾
          ⦗mem_write_reqs cd⦘.
      Global Typeclasses Opaque data.

      Definition ctrl :=
        ⦗mem_reads cd⦘⨾
          (⦗mem_reads cd⦘ ∪ (iio cd ⨾ (reg_reads_from_data cd))⁺)⨾
          iio cd⨾
          ⦗pc_writes cd⦘⨾
          instruction_order cd.
      Global Typeclasses Opaque ctrl.
    End Deps.

    (** Relates a read and a write that form an atomic update *)
    (* TODO add check on access types *)
    Definition atomic_update {et n} (cd : t et n) :=
      same_instruction_instance cd ∩ (mem_reads cd × mem_writes cd) ∩
        same_footprint cd ∩ iio cd.

  End Candidate.

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
    Definition t et unspec := ∀ n, cand et n → result string (behavior unspec).

    Module Res.
      Section Res.
        Context {et : exec_type}.
        Context {unspec : Type}.
        Notation axres := (result string (behavior unspec)).
        Notation mres := (Model.Res.t unspec).
        Notation model := (Model.nc unspec).
        Notation cand := (cand et).

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
      Context {et : exec_type}.
      Context {unspec : Type}.
      Notation axres := (result string (behavior unspec)).
      Notation mres := (Model.Res.t unspec).
      Notation model := (Model.nc unspec).
      Notation t := (t et unspec).
        Notation cand := (cand et).

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
               ∧ wf cd
               ∧ ISA_match cd isem
               ∧ to_ModelResult ax cd initSt.(MState.termCond) = Some mr
          ]}.
      #[global] Typeclasses Transparent to_Modelnc.

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
