(** This file provide an common type for representing candidate executions
    for all memory models to use *)

Require Import Ensembles.

Require Import Strings.String.

From stdpp Require Export listset.
From stdpp Require Export gmap.


Require Import SSCCommon.Common.
Require Import SSCCommon.Exec.
Require Import SSCCommon.GRel.


Require Import ISASem.Interface.

Open Scope Z_scope.
Open Scope stdpp_scope.

Module CandidateExecutions (Arch : Arch) (IA : InterfaceT Arch). (* to be imported *)
  Import Arch.
  Import IA.
  Notation outcome := (IA.outcome empOutcome).
  Notation iMon := (IA.iMon empOutcome).
  Notation iSem := (IA.iSem empOutcome).
  Notation iEvent := (IA.iEvent empOutcome).
  Notation iTrace := (IA.iTrace empOutcome).

  (* event ID *)
  Module EID.
    Record t :=
      make {
          tid : nat;
          num : N
          }.

    Global Instance eq_dec : EqDecision t.
    Proof. solve_decision. Defined.

    (* TODO Make more general automation about being countable *)
    #[local] Hint Rewrite prod_decode_encode_fst : countable.
    #[local] Hint Rewrite prod_decode_encode_snd : countable.
    #[local] Hint Rewrite @decode_encode : countable.

    Global Program Instance countable : Countable t :=
      {| encode eid := prod_encode (encode eid.(tid)) (encode eid.(num));
         decode p :=
          tid ← prod_decode_fst p ≫= decode;
          num ← prod_decode_snd p ≫= decode;
          Some (make tid num)
      |}.
    Next Obligation. sauto lq:on db:countable. Qed.

  End EID.

  Module Candidate.

    Record t :=
      make {
          events : list (iTrace ());
          (* TODO po can be deduced by the order of events in the trace *)
          (** Program order. The per-thread order of all events in the trace *)
          po : grel EID.t;
          (** Memory read from *)
          rf : grel EID.t;
          (** Memory coherence: for each pa, list of writes in order *)
          co : grel EID.t;
          (** Register read from (needed because of potentially relaxed register) *)
          rrf : grel EID.t;
          (** Same instruction, should be an equivalence relation. *)
          si : grel EID.t;
          (* TODO addr, data, and ctrl can be deduced from the dependency information in the trace *)
          (** Address dependencies *)
          addr : grel EID.t;
          (** Data dependencies *)
          data : grel EID.t;
          (** Control dependencies *)
          ctrl : grel EID.t;
        }.

    (** Get an event at a given event ID in a candidate *)
    Global Instance lookup : Lookup EID.t iEvent t :=
      fun eid cd =>
        '(trace, result) ← cd.(events) !! eid.(EID.tid);
        trace !! eid.(EID.num).

    (** This true if one of the thread had an ISA model failure
        like a Sail assertion or an Isla assumption that failed *)
    Definition failed (cd : t) : bool :=
      existsb (fun '(trace, trace_end) =>
                 match trace_end with | inr _ => true | inl _ => false end)
              cd.(events).

    (*** Accessors ***)

    Definition collect_all (P : iEvent -> bool) (cd : t) : gset EID.t :=
      ('(tid, (trace, trace_end)) ← enumerate cd.(events);
       '(num, event) ← enumerate trace;
       if P event then [EID.make tid (N.of_nat num)] else [])
        |> list_to_set.

    (** Get the set of all valid EID for that candidate *)
    Definition valid_eid (cd : t) :=
      collect_all (fun event => true) cd.


    (** Get the set of all register reads *)
    Definition reg_reads (cd : t) :=
      collect_all
        (fun event =>
           match event with
           | IEvent (RegRead _ _) _ => true
           | _ => false end)
        cd.

    (** Get the set of all register writes *)
    Definition reg_writes (cd : t) :=
      collect_all
        (fun event =>
           match event with
           | IEvent (RegWrite _ _ _ _) _ => true
           | _ => false end)
        cd.

    (** Get the set of all memory reads *)
    Definition mem_reads (cd : t) :=
      collect_all
        (fun event =>
           match event with
           | IEvent (MemRead _ _) _ => true
           | _ => false end)
        cd.

    (** Get the set of all memory writes *)
    Definition mem_write (cd : t) :=
      collect_all
        (fun event =>
           match event with
           | IEvent (MemRead _ _) _ => true
           | _ => false end)
        cd.

    (** Get the set of all barriers *)
    Definition barriers (cd : t) :=
      collect_all
        (fun event =>
           match event with
           | IEvent (Barrier _) _ => true
           | _ => false end)
        cd.

    (** Get the content of a barrier, returns none if not a barrier (or is an
        invalid EID) *)
    Definition get_barrier (cd : t) (eid : EID.t) : option barrier:=
      match cd !! eid with
      | Some (IEvent (Barrier b) ()) => Some b
      | _ => None
      end.

    (** Get the set of all TLB operations *)
    Definition tlbops (cd : t) :=
      collect_all
        (fun event =>
           match event with
           | IEvent (TlbOp _) _ => true
           | _ => false end)
        cd.

    (** Get the content of a TLB operation, returns none if not a TLB operation
        (or is an invalid EID) *)
    Definition get_tlbop (cd : t) (eid : EID.t) : option tlb_op :=
      match cd !! eid with
      | Some (IEvent (TlbOp to) ()) => Some to
      | _ => None
      end.

  End Candidate.

End CandidateExecutions.
