From RecordUpdate Require Import RecordSet.
From stdpp Require Import base strings.
Require Import bbv.Word.
Require Import Sail.Base.
From Top Require Import Ax_model_arm_vmsa_aux isa_interface_types
                        Events Execution.


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



(** Decidable equality notation that use the EqDecision type class from stdpp*)
Notation "x == y" := (bool_decide (x = y)) (at level 70, no associativity).


(** Functional pipe notation.

    TODO figure out a correct parsing level. Currently is just below relation so
    that a = b |> f will be parsed as a = (b |> f). *)
Notation "v |> f" := (f v) (at level 69, only parsing, left associativity).




(* Interface Equality decision for words (from bbv) *)
Global Instance word_eq_dec n : EqDecision (word n).
Proof.
  unfold EqDecision.
  unfold Decision.
  auto using weq.
Defined.




(* Utility functions that do not belong anywhere yet *)

(** Update a function at a specific value *)
Definition fun_add {A B} {_: EqDecision A} (k : A) (v : B) (f : A -> B) :=
  fun x : A => if k == x then v else f x.


(** A list_remove version that uses the EqDecision typeclass *)
Definition list_remove `{EqDecision A} :=
  List.remove (decide_rel (=@{A})).


(** I couldn't find this in the standard library but there should be something
somewhere. I can't be the first one to need that.*)
Fixpoint list_set {A} (n : nat) (v : A) (l : list A) :=
  match l, n with
  | nil, _ => nil
  | h :: t, 0%nat => v :: t
  | h :: t, S m => h :: (list_set m v t)
  end.




(** Execution module: Either a named error or a lists of possible outputs.

    This is used to represent non-deterministic but computational execution that
    may fail. *)
Module Exec.

  Inductive t (A : Type) :=
  | Error : string -> t A
  | Results : list A -> t A.
  Arguments Error {_} _.
  Arguments Results {_} _.

  (** Means that this execution has no output and may be safely discarded.*)
  Definition discard {A} : t A := Results [].

  (** Monadic return *)
  Definition ret {A} (a : A) : t A := Results [a].

  (** Take an option but convert None into an error *)
  Definition error_none {A} (s : string) : option A -> t A :=
    from_option ret (Error s).

  (** Take an option but convert None into a discard *)
  Definition discard_none {A} : option A -> t A :=
    from_option ret discard.

  (** Merge the results of two executions *)
  Definition merge {A} (e1 e2 : t A) :=
    match e1 with
    | Error s => Error s
    | Results l =>
      match e2 with
      | Error s => Error s
      | Results l' => Results (l ++ l')
      end
    end.

  Global Instance mret_inst : MRet t := { mret A := ret }.

  Global Instance mbind_inst : MBind t :=
    { mbind _ _ f x :=
      match x with
      | Error s => Error s
      | Results l => foldl merge discard (f <$> l)
      end }.

  Global Instance fmap_inst : FMap t :=
    { fmap _ _  f x :=
      match x with
      | Error s => Error s
      | Results l => Results (f <$> l)
      end }.
End Exec.



(** Representation of the semantics of an instruction as defined by sail.
   I don't if that's the right interface. *)
Inductive instruction_semantics :=
| ISFinished : instruction_semantics
| ISNext : forall {A : Type}, arm_outcome A -> (A -> instruction_semantics)
                       -> instruction_semantics.

(** The definition of a thread: a list of instruction *)
Definition thread_code := list instruction_semantics.

(** A program is just a list of thread. The position in the list determines the
    ThreadId. *)
Definition program := list thread_code.



(** Definition of the pc_reg that chooses the next instruction to be fetched. I
    fake ARM semantics here, so I fill divide it by 4 and use it as an index in
    the thread_code list. The execution will fail is this does not work *)
Definition pc_reg : register_name := "_PC".

(** Initial value in all registers and memory locations *)
Definition val_init : regval := wzero 64.



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
    intro H.
    destruct pa as [paspace addr].
    destruct paspace; [| done].
    unfold from_pa in H.
    simpl in H.
    case_bool_decide as He; [| done].
    unfold to_pa.
    f_equal.
    inversion H as [Hloc].
    rewrite <- He.
    autorewrite with core using reflexivity.
  Qed.

  Lemma from_to_pa (loc : t) : from_pa (to_pa loc) = Some loc.
    Opaque Word.split2.
    Opaque Word.split1.
    unfold to_pa.
    unfold from_pa.
    simpl.
    case_bool_decide as H.
    - autorewrite with core using done.
    - autorewrite with core in *. done.
  Qed.

End Loc.




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

        (* Forwarding database. The first view is the timestamp of the
           write while the second view is the max view of the dependencies
           of the write. *)
        fwdb : Loc.t -> view * view;
      }.

  Instance eta : Settable _ := settable! make
                               <prom;regs;coh;rresp;rmax;wresp;wmax;vcap;fwdb>.

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
  Definition set_fwdb (loc : Loc.t) (vs : view * view) : t -> t :=
    set fwdb (fun_add loc vs).

  (** Updates a view that from the state, by taking the max of new value and
      the current value.

      For example `update rmax vnew t` does t.rmax <- max t.rmax vnew *)
  Definition update (acc : t -> view) {_: Setter acc}
             (v : view) : t -> t :=
    set acc (max v).

  (** Return a natural that correspond to the PC in that state *)
  Definition pc (s : t) : nat := wordToNat (regs s pc_reg).1.

  (** Add a promise to the promise set *)
  Definition promise (v : view) : t -> t := set prom (fun p => v :: p).

End TState.


(** Performs a memory read at a location with a view and return possible output
    states with the timestamp and value of the read *)
Definition read_mem (loc : Loc.t) (vaddr : view) (ts : TState.t)
           (mem : Memory.t) : Exec.t (TState.t * view * regval) :=
  let vpre := max vaddr (TState.rresp ts) in
  let vread := max vpre (TState.coh ts loc) in
  let reads := Memory.read loc vread mem in
  '(time, res) ← Exec.Results reads;
  let fwd := TState.fwdb ts loc in
  let read_view := if fwd.1 == time then fwd.2 else time in
  let vpost := max vpre read_view in
  let ts := ts |> TState.update_coh loc vpost
               |> TState.update TState.rmax vpost
               |> TState.update TState.vcap vaddr
  in Exec.ret (ts, vpost, res).


(** Performs a memory write for a thread tid at a location loc with view
    vaddr and vdata. Return the new state.

    This does not need to mutate the memory as it will only fulfill an existing
    promise or discard the execution if this write can't fulfill any promises.
 *)
Definition write_mem (tid : TID.t) (loc : Loc.t) (vaddr : view)
           (vdata : view) (ts : TState.t) (mem : Memory.t) (data : regval)
  : Exec.t (TState.t):=
  let msg := Msg.make tid loc data in
  time ← Exec.discard_none $ Memory.fulfill msg (TState.prom ts) mem;
  let vpre := list_max [vaddr; vdata; TState.wresp ts; TState.vcap ts] in
  if (max vpre (TState.coh ts loc) <? time)%nat then
    ts |> set TState.prom (list_remove time)
       |> TState.update_coh loc time
       |> TState.update TState.wmax time
       |> TState.update TState.vcap vaddr
       |> TState.set_fwdb loc (time, max vaddr vdata)
       |> Exec.ret
  else
    Exec.discard.




(** Intra instruction state for propagating views inside an instruction *)
Module IIS.

  Record t :=
    make {
        rread : view; (* Max view from register reads *)
        mread : view; (* Max view from memory reads *)
        addr : view; (* View of the address dependency *)
      }.

  Instance eta : Settable _ := settable! make
                               <rread;mread;addr>.

  (** The view to used when writing a register *)
  Definition wr_view (iis : t) :=
    max (rread iis) (mread iis).

  (** Clear the rread view on dependency category change, i.e after a write
      announce. *)
  Definition clear_rread : t -> t :=
    set rread (fun _ => 0%nat).

  (** Initial IIS.t at the start of an instruction *)
  Definition start := (make 0 0 0)%nat.

  (** Updates a view that from the intra-instruction state, by taking the max of
      new value and the current value. *)
  Definition update (acc : t -> view) {_: Setter acc}
             (v : view) : t -> t :=
    set acc (max v).

End IIS.

(** Runs an outcome. This is where the main interface with outcomes is.

    The IIS is used in order to propagate view information through the outcomes.

    A set of convention is used:
    - There is only one address dependency per instructions.
      This is because all outcomes use the same address at various constant
      offsets
    - The address dependency cannot depend on a memory read by the same
      instruction, a memory read can only be used for data dependency for
      RMW instructions.
    - Any register read before a write_announce are part of the address
      dependency. The one after are part of the data dependency.

    This code is designed to work well for simple instructions but will probably
    be wrong on lots of edge-case. Unfortunately there is no clearer way of
    extracting dependencies from outcomes at the moment.

    Only 8-bytes aligned accesses are supported. *)
Definition run_outcome {A} (tid : TID.t) (o : arm_outcome A) (iis : IIS.t)
           (ts : TState.t) (mem : Memory.t) : Exec.t (IIS.t * TState.t * A) :=
  match o with
  | O_reg_write (Build_Reg_write reg val) =>
      let wr_view := IIS.wr_view iis in
      let ts := TState.set_reg reg (val, wr_view) ts in
      Exec.ret (iis, ts, ())
  | O_reg_read_request reg =>
      let (val, regt) := TState.regs ts reg in
      let iis := IIS.update IIS.rread regt iis in
      Exec.ret (iis, ts, val)
  | O_mem_read_request 8
      (Build_Mem_read_request
         _ _ _
         (AK_explicit (Build_Explicit_access_kind AV_plain AS_normal))
         None pa _ _) =>
      loc ← Exec.error_none "Invalid address" $ Loc.from_pa pa;
      '(ts, time, val) ← read_mem loc (IIS.rread iis) ts mem;
      Exec.ret (IIS.update IIS.mread time iis, ts, MR_value (val, None))
  | O_mem_write_request 8 wr =>
      match Mem_write_request_MW_access_kind wr with
      | AK_explicit (Build_Explicit_access_kind AV_plain AS_normal) =>
          let pa := Mem_write_request_MW_PA wr in
          let data := Mem_write_request_MW_value wr in
          loc ← Exec.error_none "Invalid address" $ Loc.from_pa pa;
          ts ← write_mem tid loc (IIS.addr iis) (IIS.wr_view iis) ts mem data;
          let iis := IIS.clear_rread iis in
          Exec.ret (iis, ts, MR_value None)
      | _ => Exec.Error "Unsupported non-relaxed write"
      end
  | O_mem_write_announce_address 8 _ =>
      let iis :=
        iis |> IIS.update IIS.addr (IIS.rread iis)
            |> IIS.clear_rread
      in
      Exec.ret (iis, ts, ())
  | O_branch_announce_address _ =>
      let ts := TState.update TState.vcap (IIS.wr_view iis) ts in
      Exec.ret (iis, ts, ())
  | O_barrier (BA_DxB (Build_DxB DMB _ MBReqTypes_All)) => (* dmb sy *)
      let v := max (TState.rmax ts) (TState.wmax ts) in
      let ts :=
        ts |> TState.update TState.rresp v
           |> TState.update TState.wresp v
      in
      Exec.ret (iis, ts, ())
  | O_barrier (BA_DxB (Build_DxB DMB _ MBReqTypes_Reads)) => (* dmb ld *)
      let v := TState.rmax ts in
      let ts :=
        ts |> TState.update TState.rresp v
           |> TState.update TState.wresp v
      in
      Exec.ret (iis, ts, ())
  | O_barrier (BA_DxB (Build_DxB DMB _ MBReqTypes_Writes)) => (* dmb st *)
      let ts := TState.update TState.wresp (TState.wmax ts) ts in
      Exec.ret (iis, ts, ())
  | O_barrier (BA_ISB ()) => (* isb *)
      let ts := TState.update TState.rresp (TState.vcap ts) ts in
      Exec.ret (iis, ts, ())
  | _ => Exec.Error "Unsupported outcome"
  end.


(** Run an instruction as defined by the instruction_semantics type
    by using run_outcome on all produced outcomes *)
Fixpoint run_inst (i : instruction_semantics) (iis : IIS.t) (tid : TID.t)
         (ts : TState.t) (mem : Memory.t) : Exec.t (TState.t) :=
  match i with
  | ISFinished => Exec.ret ts
  | ISNext o next =>
      '(iis, ts, res) ← run_outcome tid o iis ts mem;
      run_inst (next res) iis tid ts mem
  end.


(** Get the instruction number in the thread_code list from the pc.

    This is a very hacky way of doing fetches but it will do for now. *)
Definition inst_num_from_pc (pc : nat) : option nat :=
  if (pc mod 4 == 0)%nat then
    Some (pc / 4)%nat
  else None.


(** Run a thread by fetching an instruction and then calling run_inst *)
Definition run_thread (tid : TID.t) (tc :thread_code) (ts : TState.t)
           (mem : Memory.t) : Exec.t (TState.t) :=
  instnum ← Exec.error_none "Unaligned PC" $ inst_num_from_pc $ TState.pc ts;
  inst ← Exec.error_none "Out of bound PC" $ tc !! instnum;
  run_inst inst IIS.start tid ts mem.

(** Defines if a thread has finished execution in an ad-hoc way.
    A thread is finished if the PC is exactly one instruction beyond the end
    of the thread_code and if there is not outstanding promises. *)
Definition thread_is_finished (tc : thread_code) (ts : TState.t) :=
  (TState.pc ts = 4 * List.length tc)%nat /\ TState.prom ts = nil.

(** Defines if a thread has reached an error state (depends on memory)
    A thread has reached an error state if is has not finished but running it
    raise an error. It must also not have any outstanding promises.

    A thread that raises an error but has outstanding promises is an
    execution that can be discarded in the same way than normally finishing
    execution with outstanding promises.

    TODO: Prove that if a thread has an error, then it also has an error on
    any extension of that memory.

 *)
Definition thread_has_error (tid : TID.t) (tc : thread_code)  (ts : TState.t)
           (mem : Memory.t) :=
  ¬(thread_is_finished tc ts)
  /\ (exists err, run_thread tid tc ts mem = Exec.Error err)
  /\ TState.prom ts = nil.




(** The full machine state of promising arm *)
Module Machine.

  Definition t := (list TState.t * Memory.t)%type.


  (** Run the thread with id tid using a program in a certain machine state *)
  Definition run_id (tid : TID.t) (prog : program) (m : t)
    : Exec.t t :=
    tc ← Exec.error_none "No Thread code" $ prog !! tid;
    ts ← Exec.error_none "No Thread" $ m.1 !! tid;
    ts ← run_thread tid tc ts m.2;
    Exec.ret (list_set tid ts m.1, m.2).



  (** The steps of Promising ARM: Either make a promise or run some thread *)
  Inductive step (prog : program) (m : t) : t -> Prop :=
  | IPromise (msg : Msg.t) (ts :TState.t) :
    m.1 !! (Msg.tid msg) = Some ts ->
    let nts := TState.promise (List.length m.2 + 1)%nat ts in
    step prog m (list_set (Msg.tid msg) nts  m.1 , msg :: m.2)

  | IRun (m' : t) (tid : TID.t) (l : list t)
    : run_id tid prog m = Exec.Results l
      -> In m' l -> step prog m m'.

  (** Defines what it means for machine state to be an error state.
    This definition will probably need to be tweaked. *)
  Definition has_error (prog : program) (m : t) :=
    exists tid tc ts, prog !! tid = Some tc /\ m.1 !! tid = Some ts
                 /\ thread_has_error tid tc ts m.2.

  (** A machine state is final when all thread have properly finished *)
  Definition is_finished (prog : program) (m : t) : Prop :=
    forall tid,
      match prog !! tid with
      | None => True
      | Some tc => exists ts, m.1 !! tid = Some ts /\
                          thread_is_finished tc ts
      end.

End Machine.
