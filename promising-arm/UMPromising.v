
Require Import Strings.String.
Require Import SSCCommon.Common.
Require Import Coq.Program.Equality.

From stdpp Require Import decidable.

Require Import ISASem.ArmInst.
Require Import GenModels.TermModels.
Module TM := TermModels Arm Inst.
Import TM.
Require Import GenPromising.
Module GP := Gen Arm Inst TM.
Import GP.

(** The goal of this module is to define an User-mode promising model,
    without mixed-size on top of the new interface *)

(** This model only works for 8-bytes aligned location, as there
    in no support for mixed-sizes yet. Also all location are
    implicitly in the non-secure world.

    So in order to get the physical address you need to append 3 zeros. *)
Module Loc.
  Definition t := bv 49.

  (** Convert a location into an ARM physical address *)
  Definition to_pa (loc : t) : FullAddress :=
    {|FullAddress_paspace := PAS_NonSecure;
      FullAddress_address := bv_to_word $ bv_concat 52 loc (bv_0 3)
    |}.

  (** Recover a location from an ARM physical address. *)
  Definition from_pa (pa : FullAddress) : option t :=
    match FullAddress_paspace pa with
    | PAS_NonSecure =>
        let bvaddr := word_to_bv $ FullAddress_address pa in
        if bv_extract 0 3 bvaddr =? bv_0 3 then
          Some (bv_extract 3 49 bvaddr)
        else None
    | _ => None
    end.

  Lemma to_from_pa (pa : FullAddress) (loc : t) :
    from_pa pa = Some loc -> to_pa loc = pa.
  Proof.
    unfold from_pa,to_pa.
    hauto inv:FullAddress b!:on solve:bv_word_solve simp+:f_equal.
 Qed.

  Lemma from_to_pa (loc : t) : from_pa (to_pa loc) = Some loc.
    unfold from_pa, to_pa.
    hauto b!:on solve:bv_word_solve simp+:f_equal.
  Qed.

  (** Convert a location to a list of covered physical addresses *)
  Definition to_pas (loc : t) : list FullAddress :=
   let pa := to_pa loc in
   list_from_func 8
     (fun n => pa |> set FullAddress_address (wplus (natToWord 52 n))).

  (** Give the location containing a pa *)
  Definition from_pa_in (pa : FullAddress) : option t :=
    match FullAddress_paspace pa with
    | PAS_NonSecure =>
        let bvaddr := word_to_bv $ FullAddress_address pa in
          Some (bv_extract 3 49 bvaddr)
    | _ => None
    end.

  (** Give the index of a pa inside its containing 8-bytes word *)
  Definition pa_index (pa : FullAddress) : option (bv 3) :=
    match FullAddress_paspace pa with
    | PAS_NonSecure =>
        let bvaddr := word_to_bv $ FullAddress_address pa in
          Some (bv_extract 0 3 bvaddr)
    | _ => None
    end.

  Lemma from_pa_pa_in pa loc :
    from_pa pa = Some loc -> from_pa_in pa = Some loc.
    Proof. unfold from_pa,from_pa_in. hauto. Qed.

  Lemma from_pa_in_to_pas loc :
    ∀'pa ∈ to_pas loc, from_pa_in pa = Some loc.
  Proof.
    unfold to_pas.
    rewrite list_from_func_map.
    rewrite forall_elem_of_map.
    intros y H.
    rewrite elem_of_seq in H.
    cbn.
    f_equal.
    bv_word_solve.
  Qed.

End Loc.


(** Register and memory values (all memory access are 8 bytes aligned *)
Definition val := bv 64.

(** This is an message in the promising model memory. The location is a physical
    address as virtual memory is ignored by this model *)
Module Msg.
  Record t := make { tid : nat; loc : Loc.t; val : val }.

  #[global] Instance dec : EqDecision t.
  solve_decision.
  Defined.

End Msg.

(* TODO make naming match current latex definition *)

(** A view is just a natural *)
Definition view := nat.
Bind Scope nat_scope with view.
Global Hint Transparent view : core.
Global Hint Unfold view : core.

Module Memory.
  Import PromMemory.

  (** Representation of initial memory, this is representation
      optimized for the internals of this model, so it not a plain
      memoryMap *)
  Definition initial := Loc.t -> val.

  (** Convert from a memoryMap to the internal representation: initial *)
  Definition initial_from_memMap (mem : memoryMap) : initial :=
    fun loc => Loc.to_pas loc |> map mem |> bv_of_bytes 8 64.

  (** The promising memory: a list of events *)
  Definition t : Type := t Msg.t.

  Definition cut_after : nat -> t -> t := @cut_after Msg.t.
  Definition cut_before : nat -> t -> t := @cut_before Msg.t.



 (** Reads the last write to a location in some memory. If there was no writes,
      return the initial value val_init *)
  Fixpoint read_last (loc : Loc.t) (init : initial) (mem : t) : (view * val) :=
    match mem with
    | [] => (0%nat, init loc)
    | msg :: mem' =>
        if Msg.loc msg =? loc then
          (List.length mem, Msg.val msg)
        else read_last loc init mem'
    end.

  (** Reads from initial memory and fail, if the memory has been overwritten
      this will fail.

      This is mainly for instruction fetching in this model *)
  Definition read_initial (loc : Loc.t) (init : initial) (mem : t) : option val :=
    match read_last loc init mem with
    | (0%nat, v) => Some v
    | _ => None
    end.


  (** To a snapshot of the memory back to a memoryMap *)
  Definition to_memMap (init : initial) (mem : t) : memoryMap:=
    fun pa =>
      (loc ← Loc.from_pa_in pa;
      let '(_, v) := read_last loc init mem in
      index ← Loc.pa_index pa;
      bv_to_bytes 8 v !! bv_unsigned index)
        |> default (bv_0 8).

  (** Adds the view number to each message given a view for the last message.
      This is for convenient use with cut_after.

      TODO: it would make sense to make a function that does cut_after
      and this in a single step. *)
  Fixpoint with_views_from (v : view) (mem : t)
    : list (view * Msg.t) :=
    match mem with
    | [] => []
    | h :: q => (v,h) :: with_views_from (v - 1) q
    end.

  (** Returns the list of possible reads at a location restricted by a certain
      view. The list is never empty as one can always read from at least the
      initial value. *)
  Definition read (loc : Loc.t) (v : view) (init : initial) (mem : t)
    : list (view * val) :=
    let first := mem |> cut_before v |> read_last loc init in
    let lasts := mem |> cut_after v
                     |> with_views_from (List.length mem)
                     |> filter (fun '(v, msg) => Msg.loc msg =? loc)
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
    prom |> filter (fun t => Some msg =? mem !! t)
         |> reverse
         |> head.

  (** Check that the write at the provided timestamp is indeed to that location
      and that no write to that location have been made by any other thread *)
  Definition exclusive (loc : Loc.t) (v : view) (mem : t) : bool:=
    match mem !! v with
    | None => false
    | Some msg =>
        if Msg.loc msg =? loc then
          let tid := Msg.tid msg in
          mem |> cut_after v
              |> forallb (fun msg => (Msg.tid msg =? tid)
                                  || negb (Msg.loc msg =? loc))
        else false
    end.

End Memory.

(** The thread state *)
Module TState.

  Record t :=
    make {
        (* The promises that this thread must fullfil
           Is must be ordered with oldest promises at the bottom of the list *)
        prom : list view;

        (* regs values and views *)
        regs : reg -> regval * view;

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

  #[global] Instance eta : Settable _ :=
    settable! make <prom;regs;coh;rresp;rmax;wresp;wmax;vcap;vrel;fwdb;xclb>.

  Definition init (mem : memoryMap) (iregs : registerMap) :=
    ({|
      prom := [];
      regs := fun reg => (iregs reg, 0);
      coh := fun loc => 0;
      rresp := 0;
      rmax := 0;
      wresp := 0;
      wmax := 0;
      vcap := 0;
      vrel := 0;
      fwdb := fun loc => (0, 0, false);
      xclb := None
    |})%nat.

  (** Extract a plain register map from the thread state without views.
      This is used to decide if a thread has terminated, and to observe the
      results of the model *)
  Definition regs_only (ts : t) : registerMap :=
    fun reg => (ts.(regs) reg).1.

  (** Sets the value of a register *)
  Definition set_reg (reg : reg) (rv : reg_type * view) : t -> t
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

  (** Add a promise to the promise set *)
  Definition promise (v : view) : t -> t := set prom (fun p => v :: p).
End TState.


(** Performs a memory read at a location with a view and return possible output
    states with the timestamp and value of the read *)
Definition read_mem (loc : Loc.t) (vaddr : view) (ak : Explicit_access_kind)
           (ts : TState.t) (init : Memory.initial) (mem : Memory.t)
  : Exec.t string (TState.t * view * val) :=
  let acs := Explicit_access_kind_strength ak in
  let acv := Explicit_access_kind_variety ak in
  Exec.fail_if (acv =? AV_atomic_rmw) "Atomic RMV unsupported";;
  let vpre := max vaddr (TState.rresp ts) in
  let vpre :=
    if acs =? AS_rel_or_acq then max vpre (TState.vrel ts) else vpre in
  let vread := max vpre (TState.coh ts loc) in
  let reads := Memory.read loc vread init mem in
  '(time, res) ← Exec.Results reads;
  let fwd := TState.fwdb ts loc in
  let read_view :=
    if (fwd.1.1 =? time) && implb fwd.2 (acs =? AS_normal)
    then fwd.1.2
    else time in
  let vpost := max vpre read_view in
  let ts :=
    ts |> TState.update_coh loc time
       |> TState.update TState.rmax vpost
       |> TState.update TState.vcap vaddr
       |> (if acs =? AS_normal then id
           else (* Read acquire force the po-later access to be ordered after *)
             TState.update2 TState.rmax TState.wmax vpost)
       |> (if acv =? AV_exclusive then TState.set_xclb (time, vpost) else id)
  in Exec.ret (ts, vpost, res).

(** Performs a memory write for a thread tid at a location loc with view
    vaddr and vdata. Return the new state.

    This may mutate memory if no existing promise can be fullfilled *)
Definition write_mem (tid : nat) (loc : Loc.t) (vaddr : view) (vdata : view)
           (acs : Access_strength) (ts : TState.t) (mem : Memory.t)
           (data : val) : Exec.t string (TState.t * Memory.t * view):=
  let msg := Msg.make tid loc data in
  let '(time, mem) :=
    match Memory.fulfill msg (TState.prom ts) mem with
    | Some t => (t, mem)
    | None => Memory.promise msg mem
    end in
  let vpre := list_max [vaddr; vdata; TState.wresp ts; TState.vcap ts] in
  vpre ← (match acs with
         | AS_normal => Exec.ret $ vpre
         | AS_rel_or_acq =>
             Exec.ret $ list_max[vpre; TState.wmax ts; TState.rmax ts]
         | AS_acq_rcpc => Exec.Error "Weak write release"
         end);
  Exec.assert (max vpre (TState.coh ts loc) <? time)%nat;;
  let ts :=
    ts |> set TState.prom (delete time)
       |> TState.update_coh loc time
       |> TState.update TState.wmax time
       |> TState.update TState.vcap vaddr
       |> (if acs =? AS_normal then id
           else (* Mark the latest release to order later strong acquires*)
             TState.update TState.vrel time)
  in Exec.ret (ts, mem, time).


(** Tries to perform a memory write.

    If the store is not exclusive, the write is always performed and the second
    return value is None.

    If the store is exclusive the write may succeed or fail and the second
    return value indicate the success (true for success, false for error) *)
Definition write_mem_xcl (tid : nat) (loc : Loc.t) (vaddr : view)
           (vdata : view) (ak : Explicit_access_kind) (ts : TState.t)
           (mem : Memory.t) (data : val)
  : Exec.t string (TState.t * Memory.t):=
  let acs := Explicit_access_kind_strength ak in
  let acv := Explicit_access_kind_variety ak in
  Exec.fail_if (acv =? AV_atomic_rmw) "Atomic RMV unsupported";;
  let xcl := acv =? AV_exclusive in
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

  Record t :=
    make {
        def : view; (* The default view, comprising everything that
                       happened earlier in the instruction *)
        reads : list view (* the list of view of every values read from memory*)
      }.

  #[global] Instance eta : Settable _ :=
    settable! make <def;reads>.

  Definition init : t := make 0 [].

  (** Add a new memory read to the IIS *)
  Definition add_read (v : view) (iis : t) : t :=
    iis |> set def (max v)
        |> set reads (.++ [v]).

  (** Add a new register read to the IIS *)
  Definition add_reg (v : view) (iis : t) : t :=
    iis |> set def (max v).

  Definition from_read_deps (deps : list N) (iis : t) : view :=
   List.fold_left (fun v dep => match iis.(reads) !! dep with
                                  | Some v' => max v v'
                                  | None => v end) deps 0%nat.

  Definition from_DepOn (deps : DepOn.t) (regs: reg -> reg_type * view) (iis : t)
    : view :=
    max (from_read_deps deps.(DepOn.mem_reads) iis) $
    List.fold_left (fun v reg => max v $ (regs reg).2) deps.(DepOn.regs) 0%nat.

  Definition from_DepOn_opt (deps : option DepOn.t) regs iis :=
    match deps with
    | None => iis.(def)
    | Some deps => from_DepOn deps regs iis
    end.

End IIS.

(** Runs an outcome. *)
Definition run_outcome {A} (tid : nat) (o : outcome A) (iis : IIS.t)
           (ts : TState.t) (init : Memory.initial) (mem : Memory.t)
  : Exec.t string (IIS.t * TState.t * Memory.t * A) :=
  let deps_to_view :=
    fun deps => IIS.from_DepOn_opt deps ts.(TState.regs) iis in
  match o with
  | RegWrite reg direct deps val =>
      Exec.fail_if (negb direct) "Atomic RMV unsupported";;
      let wr_view := deps_to_view deps in
      let ts := TState.set_reg reg (val, wr_view) ts in
      Exec.ret (iis, ts, mem, ())
  | RegRead reg direct =>
      let (val, view) := ts.(TState.regs) reg in
      let iis := IIS.add_reg view iis in
      Exec.ret (iis, ts, mem, val)
  | MemRead 8 rr =>
      addr ← Exec.error_none "PA not supported" $ Loc.from_pa rr.(ReadReq.pa);
      let vaddr := deps_to_view rr.(ReadReq.addr_dep_on) in
      match rr.(ReadReq.access_kind) with
      | AK_explicit eak =>
          '(ts, view, val) ← read_mem addr vaddr eak ts init mem;
          Exec.ret (IIS.add_read view iis, ts, mem, inl (val, None))
      | AK_ifetch () => Exec.Error "TODO ifetch"
      | _ => Exec.Error "Only ifetch and explicit accesses supported"
      end
  | MemRead _ _ => Exec.Error "Memory read of size other than 8"
  | MemWrite 8 wr =>
      addr ← Exec.error_none "PA not supported" $ Loc.from_pa wr.(WriteReq.pa);
      let vaddr := deps_to_view wr.(WriteReq.addr_dep_on) in
      let data := wr.(WriteReq.value) in
      let vdata := deps_to_view wr.(WriteReq.data_dep_on) in
      match wr.(WriteReq.access_kind) with
      | AK_explicit eak =>
          '(ts, mem) ← write_mem_xcl tid addr vaddr vdata eak ts mem data;
          Exec.ret (iis, ts, mem, inl None)
      | AK_ifetch () => Exec.Error "Write of type ifetch ???"
      | AK_ttw () => Exec.Error "Write of type TTW ???"
      | _ => Exec.Error "Unsupported non-explicit write"
      end
  | BranchAnnounce _ deps =>
      let ts := TState.update TState.vcap (deps_to_view deps) ts in
      Exec.ret (iis, ts, mem, ())
  | Barrier (Barrier_DMB dmb) => (* dmb *)
      match dmb.(DxB_types) with
      | MBReqTypes_All (* dmb sy *) =>
          let v := max (TState.rmax ts) (TState.wmax ts) in
          let ts :=
            ts |> TState.update TState.rresp v
              |> TState.update TState.wresp v
          in
          Exec.ret (iis, ts, mem, ())
      | MBReqTypes_Reads (* dmb ld *) =>
          let v := TState.rmax ts in
          let ts :=
            ts |> TState.update TState.rresp v
              |> TState.update TState.wresp v
          in
          Exec.ret (iis, ts, mem, ())
      | MBReqTypes_Writes (* dmb st *) =>
          let ts := TState.update TState.wresp (TState.wmax ts) ts in
          Exec.ret (iis, ts, mem, ())
      end
  | Barrier (Barrier_ISB ()) => (* isb *)
      let ts := TState.update TState.rresp (TState.vcap ts) ts in
      Exec.ret (iis, ts, mem, ())
  | GenericFail s => Exec.Error ("Instruction failure: " ++ s)
  | Choose n =>
      v ← Exec.choose (bv n);
      Exec.ret(iis, ts, mem, v)
  | Discard => Exec.discard
  | _ => Exec.Error "Unsupported outcome"
  end.


(** Runs an instruction as defined by the instruction_semantics type by using
    run_outcome on all produced outcomes.*)
Fixpoint run_iSem (i : iSem) (iis : IIS.t) (tid : nat)
         (ts : TState.t) (init : Memory.initial) (mem : Memory.t)
  : Exec.t string (TState.t * Memory.t) :=
  match i with
  | Ret () => Exec.ret (ts, mem)
  | Next o next =>
      '(iis, ts, mem, res) ← run_outcome tid o iis ts init mem;
      run_iSem (next res) iis tid ts init mem
  end.

Local Notation pthread_t := (PThread.t TState.t Msg.t).

(** Same as run_iSem but from a pthread *)
Definition run_pthread (i : iSem) (pthread : pthread_t) :=
  run_iSem i IIS.init
    pthread.(PThread.tid)
    pthread.(PThread.tstate)
    (pthread.(PThread.initmem) |> Memory.initial_from_memMap)
    pthread.(PThread.events).


(* A thread is allowed to promise any promises with the correct tid.
   This a non-certified promising model *)
Definition allowed_promises_nocert (i : iSem) (pthread : pthread_t) :=
  fun msg => msg.(Msg.tid) = pthread.(PThread.tid).

Definition emit_promise' (i : iSem) (pthread : pthread_t) (msg : Msg.t) :=
  let vmsg := length pthread.(PThread.events) in
  pthread.(PThread.tstate) |> TState.promise vmsg.

Definition memory_snapshot' (memMap : memoryMap) (mem : Memory.t) : memoryMap :=
  Memory.to_memMap (Memory.initial_from_memMap memMap) mem.

Definition user_mode_promising_nocert : PromisingModel :=
  {|tState := TState.t;
    tState_init := TState.init;
    tState_regs := TState.regs_only;
    mEvent := Msg.t;
    run_instr := run_pthread;
    allowed_promises := allowed_promises_nocert;
    emit_promise := emit_promise';
    memory_snapshot := memory_snapshot';
  |}.

(* TODO defined certified version. In theory, only "allowed_promises" needs to
change *)
