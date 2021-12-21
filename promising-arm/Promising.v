(* This file provides a definition of the Promising ARM model, as defined in the
   corresponding PLDI'19 paper by Christopher Pulte, Jean Pichon-Pharabod,
   Jeehoon Kang, Sung-Hwan Lee, Chung-Kil Hur.

   The main differences with the other implementation at
   https://github.com/snu-sf/promising-arm are:

   - The extra standard library used is stdpp (as this is intended to work with
     Iris later)

   - The language over which the model is defined is the Sail outcome language.
     It is simulated as an assembly-like language with each instruction
     modifying the PC at which the next instruction is fetched. Termination is
     simulated by having the PC point to the instruct one-past-the-end of the
     instruction array.

   - This model is much more computational: All the inner thread execution is
     computational, only the promising step is not.

   Unfortunately all this changes made it so that very little code of the
   previous implementation is reusable. I tried to keep the names of the
   previous implementation when talking about the same object defined in the
   paper.

   Currently this implementation does not handle exclusive accesses,
   and acquire-release accesses *)

From Hammer Require Import Tactics.
Require Import Common.
Require Import PRelations.
Require Exec.
Import Exec.Tactics.
Require Import Sail.Base.
From Top Require Import Ax_model_arm_vmsa_aux isa_interface_types
     Events Execution.







(** This model only works for 8-bytes aligned location, as there
    in no support for mixed-sizes yet. Also all location are
    implicitly in the non-secure world.

    So in order to get the physical address you need to append 3 zeros. *)
Module Loc.
  Definition t := word 49.

  (** Convert a location into an ARM physical address *)
  Definition to_pa (loc : t) : FullAddress :=
    {|FullAddress_paspace := PAS_NonSecure;
      FullAddress_address := Word.combine loc (wzero 3)
    |}.

  (** Recover a location from an ARM physical address. *)
  Definition from_pa (pa : FullAddress) : option t :=
    match FullAddress_paspace pa with
    | PAS_Secure => None
    | PAS_NonSecure =>
        if Word.split2 49 3 (FullAddress_address pa) == wzero 3 then
          Some (Word.split1 49 3 (FullAddress_address pa))
        else None
    end.

  Lemma to_from_pa (pa : FullAddress) (loc : t) :
    from_pa pa = Some loc -> to_pa loc = pa.
    Opaque Word.split2.
    Opaque Word.split1.
    unfold from_pa,to_pa.
    sauto lb:on db:core.
  Qed.

  Lemma from_to_pa (loc : t) : from_pa (to_pa loc) = Some loc.
    Opaque Word.split2.
    Opaque Word.split1.
    unfold from_pa,to_pa.
    sauto lb:on db:core.
  Qed.

End Loc.

(** In the remaining code, dependencies are represented as a list of naturals
    When running an instruction, each action that produces a dependency is
    numbered. Such actions include reading a register or producing a value from
    memory

    See Outcome.produces_dependency
 *)
Definition dependencies := list nat.


(** A request for a memory read *)
Module ReadRequest.
  Record t := make {
      addr : Loc.t;
      addr_deps: dependencies;
      access_kind : Access_kind}.

  Definition from_sail (mwr : Mem_read_request 8 vasize_ArmA pa_ArmA) : t.
    (* I cannot do this without a extra description of dependencies *)
    admit.
    Admitted.

End ReadRequest.

(** A request for a memory write *)
Module WriteRequest.
  Record t := make {
      addr : Loc.t;
      addr_deps: dependencies;
      data : regval;
      data_deps : dependencies;
      access_kind : Access_kind}.

  Definition from_sail (mwr : Mem_write_request 8 vasize_ArmA pa_ArmA) : t.
    (* I cannot do this without a extra description of dependencies *)
    admit.
    Admitted.

End WriteRequest.

(** This model has a custom outcome type that provides explicit dependency
    information.

    This outcome type also restrict behaviors to what the model supports.
    If you are translation from another semantics to this one and the
    semantics isn't in this type, it isn't supported by the model.
    In which case you should use Fail with an appropriate error message. *)
Module Outcome.

  Inductive t : Type -> Type :=
  (* Reads a value and returns it. Creates a new possible dependency on the read
     value that other outcome can depend on. *)
  | MemRead : ReadRequest.t -> t regval
  (* Writes a value to memory. If the requested write was exclusive and this was
   no possible, this execution is aborted. It expected of instruction to handle
   the possible failure themselves. *)
  | MemWrite : WriteRequest.t -> t unit
  (* Signals a non trivial branching instruction. This means that this branch
     create a control-flow dependency to a set of dependencies as specified in
     the second field. The first value is the new target. *)
  | Branch : regval -> dependencies -> t unit
  (* An ARM barrier *)
  | Barrier : barrier_ArmA -> t unit
  (* Reads a register. Creates a new possible dependency that other outcome can
     depend on.*)
  | RegRead : register_name -> t regval
  (* Writes a register. Provides the set of values this write depends on *)
  | RegWrite : register_name -> regval -> dependencies -> t unit
  (* Chooses non deterministically a bit vector of a certain size *)
  | Choose (n : nat) : t (word n)
  (* Fails with an error message *)
  | Fail : string -> t False.

  Definition produces_dependency {A : Type} (o : t A) : bool :=
    match o with
    | MemRead _ => true
    | RegRead _ => true
    | _ => false
    end.

End Outcome.

(** Representation of the semantics of an instruction as defined by sail.
   I don't if that's the right interface. *)
Inductive instruction_semantics :=
| ISFinished : instruction_semantics
| ISNext : forall {A : Type}, arm_outcome A -> (A -> instruction_semantics)
                       -> instruction_semantics.


(** The semantics of instruction with the new outcome type

    TODO: Presenting this as a monad will ease the writing of custom
    instructions *)
Module Inst.
  Inductive t :=
  | Finished : t
  | Next : forall {A : Type}, Outcome.t A -> (A -> t) -> t.

  Definition from_sail  (is : instruction_semantics) : t.
    (* I cannot do this without a extra description of dependencies *)
  admit.
  Admitted.
End Inst.


(** The definition of a thread: a list of instruction *)
Definition thread_code := list Inst.t.

(** A program is just a list of threads. The position in the list determines the
    ThreadId. *)
Definition program := list thread_code.



(** Definition of the pc_reg that chooses the next instruction to be fetched. I
    fake ARM semantics here, so I fill divide it by 4 and use it as an index in
    the thread_code list. The execution will fail is this does not work *)
Definition pc_reg : register_name := "_PC".

(** Initial value in all registers and memory locations *)
Definition val_init : regval := wzero 64.





(** Sail Thread ids are defined in a complex way. Plain nat are simpler. This
 module provides plain nat as tid with conversion functions *)
Module TID.
  Definition t := nat.

  Definition from_sail (id : ThreadId) : t.
    destruct id. apply Z.to_nat. assumption.
  Defined.

  Definition to_sail (id : t) : ThreadId.
    exists (Z.of_nat id).
    unfold ArithFact.
    apply Build_ArithFactP.
    apply Z.geb_le.
    apply Zle_0_nat.
  Defined.

End TID.




(** This is an message in the promising model memory. The location is a physical
    address as I ignore virtual memory for now *)
Module Msg.
  Record t := make { tid : TID.t; loc : Loc.t; val : regval }.

  Global Instance dec : EqDecision t.
  solve_decision.
  Defined.

End Msg.


(** A view is just a natural *)
Definition view := nat.


(** The promising arm memory system. *)
Module Memory.

  (* I'm using a simple list representation. The most recent write is the head
     of the list. *)
  Definition t := list Msg.t.

  (** Definition of the memory numbering. So it can be used with the !! operator
   *)
  Global Instance lookup_inst : Lookup nat Msg.t Memory.t :=
    { lookup k mem :=
      if k == 0%nat then None
      else
        let len := List.length mem in
        if (len <? k)%nat then
          List.nth_error mem (len - k)%nat
        else
          None
    }.

  (** Cuts the memory to only the memory that exists before the view, included.
   *)
  Definition cut_before (v : view) (mem : t) : t :=
    let len := List.length mem in
    (* Here I'm using the m - n = 0 when n > m behavior *)
    drop (len - v) mem.

  (** Cuts the memory to only the memory that exists after the view, excluded.
   *)
  Definition cut_after (v : view) (mem : t) : t :=
    let len := List.length mem in take (len - v) mem.


  (** Reads the last write to a location in some memory. If there was no writes,
      return the initial value val_init *)
  Fixpoint read_last (loc : Loc.t) (mem : t) : (view * regval) :=
    match mem with
    | [] => (0%nat, val_init)
    | msg :: mem' =>
        if Msg.loc msg == loc then
          (List.length mem, Msg.val msg)
        else read_last loc mem'
    end.

  (** Adds the view number to each message given a view for the last message. *)
  Fixpoint with_views_from (v : view) (mem : t)
    : list (view * Msg.t) :=
    match mem with
    | [] => []
    | h :: q => (v,h) :: with_views_from (v - 1)%nat q
    end.

  (** Returns the list of possible reads at a location restricted by a certain
      view. The list is never empty as one can always read from at least the
      initial value. *)
  Definition read (loc : Loc.t) (v : view) (mem : t)
    : list (view * regval) :=
    let first := mem |> cut_before v |> read_last loc in
    let lasts := mem |> cut_after v
                     |> with_views_from (List.length mem)
                     |> filter (fun '(v, msg) => Msg.loc msg == loc)
                     |> map (fun '(v, msg) => (v, Msg.val msg))
    in
    lasts ++ [first].

  (** Promise a write and add it at the end of memory *)
  Definition promise (msg : Msg.t) (mem : t) : view * t :=
    let nmem := msg :: mem in (List.length nmem, nmem).

  (** Returns a view among a promise set that correspond to a message. The
      oldest matching view is taken. This is because it can be proven that
      taking a more recent view, will make the previous promises unfulfillable
      and thus the corresponding executions would be discarded. TODO prove it.
      *)
  Definition fulfill (msg : Msg.t) (prom : list view) (mem : t) : option view :=
    prom |> filter (fun t => Some msg == mem !! t)
         |> reverse
         |> head.

  (** Check that the write at the provided timestamp is indeed to that location
      and that no write to that location have been made by any other thread *)
  Definition exclusive (loc : Loc.t) (v : view) (mem : t) : bool:=
    match mem !! v with
    | None => false
    | Some msg =>
        if Msg.loc msg == loc then
          let tid := Msg.tid msg in
          mem |> cut_after v
              |> forallb (fun msg => (Msg.tid msg == tid)
                                  || negb (Msg.loc msg == loc))
        else false
    end.

End Memory.


(** The thread state.

    This module was named `Local` in the original implementation. *)
Module TState.

  Record t :=
    make {
        (* The promises that this thread must fullfil
           Is must be ordered with oldest promises at the bottom of the list *)
        prom : list view;

        (* regs values and views *)
        regs : register_name -> regval * view;

        (* The coherence views *)
        coh : Loc.t -> view;

        rresp : view; (* The view all reads must respect. vrnew in the paper *)
        rmax : view; (* The maximum output view of a read. vrold in the paper *)
        wresp : view; (* The view all write must respect. vwnew in the paper *)
        wmax : view; (* The maximum view of a write. vwold in the paper *)
        vcap : view; (* control-flow + addr-po view *)
        vrel : view; (* post view of the last write release *)

        (* Forwarding database. The first view is the timestamp of the
           write while the second view is the max view of the dependencies
           of the write. The boolean marks if the store was an exclusive*)
        fwdb : Loc.t -> view * view * bool;

        (* Exclusive database. If there was a recent load exclusive but the
           corresponding store exclusive has not yet run, this will contain
           the timestamp and post-view of the load exclusive*)
        xclb : option (view * view);
      }.

  Instance eta : Settable _ :=
    settable! make <prom;regs;coh;rresp;rmax;wresp;wmax;vcap;vrel;fwdb;xclb>.

  (** Sets the value of a register *)
  Definition set_reg (reg : register_name) (rv : regval * view) : t -> t
    := set regs (fun_add reg rv).

  (** Sets the coherence view of a location *)
  Definition set_coh (loc : Loc.t) (v : view) : t -> t :=
    set coh (fun_add loc v).

  (** Updates the coherence view of a location by taking the max of the new
      view and of the existing value *)
  Definition update_coh (loc : Loc.t) (v : view) (s : t) : t :=
    set_coh loc (max v (coh s loc)) s.

  (** Updates the forwarding database for a location. *)
  Definition set_fwdb (loc : Loc.t) (vs : view * view * bool) : t -> t :=
    set fwdb (fun_add loc vs).

  (** Set the exclusive database to the timestamp and view of the latest
      load exclusive *)
  Definition set_xclb (vs : view * view) : t -> t :=
    set xclb (fun _ => Some vs).

  (** Clear the exclusive database, to mark a store exclusive *)
  Definition clear_xclb : t -> t :=
    set xclb (fun _ => None).

  (** Updates a view that from the state, by taking the max of new value and
      the current value.

      For example `update rmax vnew t` does t.rmax <- max t.rmax vnew *)
  Definition update (acc : t -> view) {_: Setter acc}
             (v : view) : t -> t :=
    set acc (max v).

  (** Updates two view in the same way as update. Purely for convenience *)
  Definition update2 (acc1 acc2 : t -> view) {_: Setter acc1} {_: Setter acc2}
             (v : view) : t -> t :=
    (update acc1 v) ∘ (update acc2 v).

  (** Return a natural that correspond to the PC in that state *)
  Definition pc (s : t) : nat := wordToNat (regs s pc_reg).1.

  (** Add a promise to the promise set *)
  Definition promise (v : view) : t -> t := set prom (fun p => v :: p).

End TState.

(** Performs a memory read at a location with a view and return possible output
    states with the timestamp and value of the read *)
Definition read_mem (loc : Loc.t) (vaddr : view) (ak : Explicit_access_kind)
           (ts : TState.t) (mem : Memory.t)
  : Exec.t string (TState.t * view * regval) :=
  let acs := Explicit_access_kind_EAK_strength ak in
  let acv := Explicit_access_kind_EAK_variety ak in
  Exec.fail_if (acv == AV_atomicRMW) "Atomic RMV unsupported";;
  let vpre := max vaddr (TState.rresp ts) in
  let vpre :=
    if acs == AS_Rel_or_Acq then max vpre (TState.vrel ts) else vpre in
  let vread := max vpre (TState.coh ts loc) in
  let reads := Memory.read loc vread mem in
  '(time, res) ← Exec.Results reads;
  let fwd := TState.fwdb ts loc in
  let read_view :=
    if (fwd.1.1 == time) && implb fwd.2 (acs == AS_normal)
    then fwd.1.2
    else time in
  let vpost := max vpre read_view in
  let ts :=
    ts |> TState.update_coh loc time
       |> TState.update TState.rmax vpost
       |> TState.update TState.vcap vaddr
       |> (if acs == AS_normal then id
           else (* Read acquire force the po-later access to be ordered after *)
             TState.update2 TState.rmax TState.wmax vpost)
       |> (if acv == AV_exclusive then TState.set_xclb (time, vpost) else id)
  in Exec.ret (ts, vpost, res).

(** Performs a memory write for a thread tid at a location loc with view
    vaddr and vdata. Return the new state.

    This may mutate memory if no existing promise can be fullfilled *)
Definition write_mem (tid : TID.t) (loc : Loc.t) (vaddr : view) (vdata : view)
           (acs : Access_strength) (ts : TState.t) (mem : Memory.t)
           (data : regval) : Exec.t string (TState.t * Memory.t * view):=
  let msg := Msg.make tid loc data in
  let '(time, mem) :=
    match Memory.fulfill msg (TState.prom ts) mem with
    | Some t => (t, mem)
    | None => Memory.promise msg mem
    end in
  let vpre := list_max [vaddr; vdata; TState.wresp ts; TState.vcap ts] in
  vpre ← (match acs with
         | AS_normal => Exec.ret $ vpre
         | AS_Rel_or_Acq =>
             Exec.ret $ list_max[vpre; TState.wmax ts; TState.rmax ts]
         | AS_AcqRCpc => Exec.Error "Weak write release"
         end);
  Exec.assert (max vpre (TState.coh ts loc) <? time)%nat;;
  let ts :=
    ts |> set TState.prom (list_remove time)
       |> TState.update_coh loc time
       |> TState.update TState.wmax time
       |> TState.update TState.vcap vaddr
       |> (if acs == AS_normal then id
           else (* Mark the latest release to order later strong acquires*)
             TState.update TState.vrel time)
  in Exec.ret (ts, mem, time).


(** Tries to perform a memory write.

    If the store is not exclusive, the write is always performed and the second
    return value is None.

    If the store is exclusive the write may succeed or fail and the second
    return value indicate the success (true for success, false for error) *)
Definition write_mem_xcl (tid : TID.t) (loc : Loc.t) (vaddr : view)
           (vdata : view) (ak : Explicit_access_kind) (ts : TState.t)
           (mem : Memory.t) (data : regval)
  : Exec.t string (TState.t * Memory.t):=
  let acs := Explicit_access_kind_EAK_strength ak in
  let acv := Explicit_access_kind_EAK_variety ak in
  Exec.fail_if (acv == AV_atomicRMW) "Atomic RMV unsupported";;
  let xcl := acv == AV_exclusive in
  if xcl then
    '(ts, mem, time) ← write_mem tid loc vaddr vdata acs ts mem data;
    match TState.xclb ts with
    | None => Exec.discard
    | Some (xtime, xview) =>
        Exec.assert $ Memory.exclusive loc xtime (Memory.cut_after time mem)
    end;;
    let ts := TState.set_fwdb loc (time, max vaddr vdata, true) ts in
    Exec.ret (TState.clear_xclb ts, mem)
  else
    '(ts, mem, time) ← write_mem tid loc vaddr vdata acs ts mem data;
    let ts := TState.set_fwdb loc (time, max vaddr vdata, false) ts in
    Exec.ret (ts, mem).


(** Intra instruction state for propagating views inside an instruction *)
Module IIS.

  Definition t := list view.


  Definition start : t := [].

  Check List.fold_left.

  Definition from_deps (deps : list nat) (iis : t) : view :=
   List.fold_left (fun v dep => match iis !! dep with
                                  | Some v' => max v v'
                                  | None => v end) deps 0%nat.


  Definition add_dep (v : view) (iis :t) : t :=
    (iis ++ [v])%list.

End IIS.

(** Runs an outcome. *)
Definition run_outcome {A} (tid : TID.t) (o : Outcome.t A) (iis : IIS.t)
           (ts : TState.t) (mem : Memory.t)
  : Exec.t string (IIS.t * TState.t * Memory.t * A) :=
  match o with
  | Outcome.RegWrite reg val deps =>
      let wr_view := IIS.from_deps deps iis in
      let ts := TState.set_reg reg (val, wr_view) ts in
      Exec.ret (iis, ts, mem, ())
  | Outcome.RegRead reg =>
      let (val, view) := TState.regs ts reg in
      let iis := IIS.add_dep view iis in
      Exec.ret (iis, ts, mem, val)
  | Outcome.MemRead (ReadRequest.make addr addr_deps (AK_explicit ak)) =>
      '(ts, time, val) ← read_mem addr (IIS.from_deps addr_deps iis) ak ts mem;
      Exec.ret (IIS.add_dep time iis, ts, mem, val)
  | Outcome.MemWrite wr =>
      match WriteRequest.access_kind wr with
      | AK_explicit ak =>
          let addr := WriteRequest.addr wr in
          let data := WriteRequest.data wr in
          let vaddr := IIS.from_deps (WriteRequest.addr_deps wr) iis in
          let vdata := IIS.from_deps (WriteRequest.data_deps wr) iis in
          '(ts, mem) ← write_mem_xcl tid addr vaddr vdata ak ts mem data;
          Exec.ret (iis, ts, mem, ())
      | _ => Exec.Error "Unsupported non-explicit write"
      end
  | Outcome.Branch _ deps =>
      let ts := TState.update TState.vcap (IIS.from_deps deps iis) ts in
      Exec.ret (iis, ts, mem, ())
  | Outcome.Barrier (BA_DxB (Build_DxB DMB _ MBReqTypes_All)) => (* dmb sy *)
      let v := max (TState.rmax ts) (TState.wmax ts) in
      let ts :=
        ts |> TState.update TState.rresp v
           |> TState.update TState.wresp v
      in
      Exec.ret (iis, ts, mem, ())
  | Outcome.Barrier (BA_DxB (Build_DxB DMB _ MBReqTypes_Reads)) => (* dmb ld *)
      let v := TState.rmax ts in
      let ts :=
        ts |> TState.update TState.rresp v
           |> TState.update TState.wresp v
      in
      Exec.ret (iis, ts, mem, ())
  | Outcome.Barrier (BA_DxB (Build_DxB DMB _ MBReqTypes_Writes)) => (* dmb st *)
      let ts := TState.update TState.wresp (TState.wmax ts) ts in
      Exec.ret (iis, ts, mem, ())
  | Outcome.Barrier (BA_ISB ()) => (* isb *)
      let ts := TState.update TState.rresp (TState.vcap ts) ts in
      Exec.ret (iis, ts, mem, ())
  | _ => Exec.Error "Unsupported outcome"
  end.

(** Runs an instruction as defined by the instruction_semantics type by using
    run_outcome on all produced outcomes.*)
Fixpoint run_inst (i : Inst.t) (iis : IIS.t) (tid : TID.t)
         (ts : TState.t) (mem : Memory.t)
  : Exec.t string (TState.t * Memory.t) :=
  match i with
  | Inst.Finished => Exec.ret (ts, mem)
  | Inst.Next o next =>
      '(iis, ts, mem, res) ← run_outcome tid o iis ts mem;
      run_inst (next res) iis tid ts mem
  end.

(** Get the instruction number in the thread_code list from the pc.

    This is a very hacky way of doing fetches but it will do for now. *)
Definition inst_num_from_pc (pc : nat) : option nat :=
  if (pc mod 4 == 0)%nat then
    Some (pc / 4)%nat
  else None.

Module Thread.
  Record t :=
    make {
        tid : TID.t;
        code : thread_code;
        state : TState.t;
        mem : Memory.t
      }.
  Instance eta : Settable _ :=
    settable! make <tid; code; state; mem>.

  (** Run a thread by fetching an instruction and then calling run_inst. *)
  Definition run (thr : t) : Exec.t string t :=
    instnum ← Exec.error_none "Unaligned PC" $ inst_num_from_pc $
            TState.pc $ state thr;
    inst ← Exec.error_none "Out of bound PC" $ (code thr) !! instnum;
    '(ts, mem) ← run_inst inst IIS.start (tid thr) (state thr) (mem thr);
    Exec.ret {|tid := tid thr; code := code thr; state := ts; mem := mem|}.

  Lemma run_tid thr thr' :
    Exec.In thr' (run thr) -> tid thr' = tid thr.
  Proof. unfold run. hauto simp+:exec_simp. Qed.

  Lemma run_code thr thr' :
    Exec.In thr' (run thr) -> code thr' = code thr.
  Proof. unfold run. hauto simp+:exec_simp. Qed.

  Definition promise (msg : Msg.t) (thr : t) : t :=
    let (t, nmem) := Memory.promise msg (mem thr) in
    thr |> set state $ TState.promise t
        |> set mem (fun _ => nmem).

  Lemma promise_tid msg thr : tid (promise msg thr) = tid thr.
    Proof. by unfold promise. Qed.

  Lemma promise_code msg thr : code (promise msg thr) = code thr.
    Proof. by unfold promise. Qed.

  (** Defines if a thread has finished execution in an ad-hoc way.
      A thread is finished if the PC is exactly one instruction beyond the end
      of the thread_code and if there is not outstanding promises. *)
  Definition is_finished (thr : t) :=
    (TState.pc (state thr) = 4 * List.length (code thr))%nat
    /\ TState.prom (state thr) = nil.

  (** Defines if a thread has reached an error state (depends on memory)
      A thread has reached an error state if is has not finished but running it
      raise an error. It must also not have any outstanding promises.

      A thread that raises an error but has outstanding promises is an
      execution that can be discarded in the same way than normally finishing
      execution with outstanding promises.

      TODO: Prove that if a thread has an error, then it also has an error on
      any extension of that memory by other threads *)
  Definition has_error (thr : t) :=
    ¬(is_finished thr)
    /\ (exists err, run thr = Exec.Error err)
    /\ TState.prom (state thr) = nil.

  Inductive certified (thr : t) : Prop :=
  | CertNoProm : TState.prom (state thr) = nil -> certified thr
  | CertNext thr': Exec.In thr' (run thr) -> certified thr' ->
                     certified thr.
  Global Hint Constructors certified : core.

  Fixpoint certifiedb (fuel : nat) (thr : t) : bool :=
    if TState.prom (state thr) == nil then true else
      match fuel with
      | 0%nat => false
      | S m =>
          match run thr with
          | Exec.Error _ => false
          | Exec.Results l => existsb (certifiedb m) l
          end
      end.


  Lemma certifiedb_sound (thr : t) :
    certified thr <-> exists fuel : nat, certifiedb fuel thr.
  Proof.
    split.
    - induction 1 as [ | ? ? Hrun Hc].
      + exists 0%nat. qauto lb:on.
      + destruct IHHc as [fuel Hcb].
        exists (S fuel).
        sauto inv:Exec.In lqb:on.
    - destruct 1 as [fuel Hcb].
      generalize dependent thr.
      induction fuel; hauto ctrs:certified,Exec.In lqb:on.
  Qed.

  Inductive step (thr : t) : t -> Prop :=
  | SPromise (msg : Msg.t) : step thr (Thread.promise msg thr)
  | SRun (thr' : t) : Exec.In thr' (run thr) -> step thr thr'.

  Lemma step_tid thr thr' : step thr thr' -> tid thr = tid thr'.
  Proof. hauto use:run_tid, promise_tid inv:step. Qed.

  Lemma step_code thr thr' : step thr thr' -> code thr = code thr'.
  Proof. hauto use:run_code, promise_code inv:step. Qed.

  Definition cstep : relation t := fun thr thr' =>
    step thr thr' /\ certified thr'.

  Lemma cstep_in_step : cstep ⊆ step.
    Proof. hauto lq:on db:rels. Qed.

End Thread.



(** The full machine state of promising arm *)
Module Machine.

  Definition t := (list TState.t * Memory.t)%type.

  Definition get_thread (tid :TID.t) (prog : program) (m : t)
    : option Thread.t :=
    code ← prog !! tid;
    ts ← m.1 !! tid;
    Some {|Thread.tid := tid;
           Thread.code := code;
           Thread.state := ts;
           Thread.mem := m.2 |}.

  Definition set_thread (thr : Thread.t) (m : t) : t :=
    (list_set (Thread.tid thr) (Thread.state thr) m.1, Thread.mem thr).

  (** Run the thread with id tid using a program in a certain machine state *)
  Definition run_id (tid : TID.t) (prog : program) (m : t)
    : Exec.t string t :=
    thr ← Exec.error_none "No Thread" $ get_thread tid prog m;
    thr ← Thread.run thr;
    Exec.ret $ set_thread thr m.


  Inductive step_thread (tid : TID.t) (prog : program) (m : t) : t -> Prop :=
  | StepThread (code : thread_code) thr thr':
    prog !! tid = Some code ->
    get_thread tid prog m = Some thr ->
    Thread.step thr thr' ->
    step_thread tid prog m (set_thread thr' m).

  Definition step (prog : program) (m m' : t) : Prop :=
    exists (tid : TID.t), step_thread tid prog m m'.

  Inductive cstep_thread (tid : TID.t) (prog : program) (m : t)
    : t -> Prop :=
  | CStepThread (code : thread_code) thr thr':
    prog !! tid = Some code ->
    get_thread tid prog m = Some thr ->
    Thread.cstep thr thr' ->
    cstep_thread tid prog m (set_thread thr' m).

  Definition cstep (prog : program) (m m' : t) : Prop :=
    exists (tid : TID.t), step_thread tid prog m m'.


  (** Defines what it means for machine state to be an error state.
    This definition will probably need to be tweaked. *)
  Definition has_error (prog : program) (m : t) :=
    exists tid thr, get_thread tid prog m = Some thr /\ Thread.has_error thr.

  (** A machine state is final when all thread have properly finished *)
  Definition is_finished (prog : program) (m : t) : Prop :=
    forall tid,
    match get_thread tid prog m with
    | None => True
    | Some thr => Thread.is_finished thr
    end.

End Machine.



Section Certification.
  Open Scope rels_scope.

  Parameter prog : program.

  (* In the original model, this was promise_step_certified in CertifyComplete.
     This is where most of the complexity will happen *)
  Lemma promise_step_certified msg thr :
    Thread.certified (Thread.promise msg thr) -> Thread.certified thr.
  Admitted.

  Lemma step_finished_certified (y z : Thread.t) :
    Thread.is_finished z -> Thread.step^* y z -> Thread.certified y.
  Proof.
    intros Hf Hs.
    eapply clos_refl_trans_ind_right; [| | exact Hs]; [firstorder |].
    clear dependent y.
    intros x y Hs Hc Hss.
    destruct Hs.
    - by eapply promise_step_certified.
    - by eapply Thread.CertNext.
  Qed.

  Ltac rtc_transfer_right H :=
    match type of H with
    | ?R^* ?a ?b => pattern a; apply (clos_refl_trans_ind_right _ R _ b);
                   [| | exact H]; clear dependent a
    end.

  Lemma certified_thread_equiv :
    forall thr thr' : Thread.t,
    Thread.is_finished thr' ->
    (Thread.step^* thr thr' <-> Thread.cstep^* thr thr').
    intros ? ? H. split.
    - intro Hs.
      rtc_transfer_right Hs; sauto lq:on use:step_finished_certified.
    - hauto l:on use:Rel.inclusion_rt_rt, Thread.cstep_in_step db:rels.
  Qed.

  Lemma certified_equiv (m m' : Machine.t) :
    Machine.is_finished prog m' ->
    ((Machine.step prog)^* m m' <-> (Machine.cstep prog)^* m m').
  Proof.
  Admitted.

End Certification.
