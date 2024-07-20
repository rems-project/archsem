Require Import ArmInst.
Require Import SSCCommon.Options.
Require Import SSCCommon.Common.
Require Import SSCCommon.Exec.
Require Import SSCCommon.StateT.
Require Import SSCCommon.Effects.

Section Seq.

Context {deps : Type} (regs_whitelist : option (gset reg)).

(** A sequential state for bookkeeping reads and writes to registers/memory in
    gmaps, as well as, the initial state *)
Record seq_state := {
  initSt : MState.init 1;
  mem : gmap pa (bv 8);
  regs : gmap reg regval;
}.

Global Instance eta_seq_state : Settable seq_state :=
  settable! Build_seq_state <initSt;mem;regs>.

Notation seqmon := (stateT seq_state (Exec.t string)).

Definition read_reg_seq_state (reg : reg) (seqst : seq_state) : regval :=
  if (seqst.(regs) !! reg) is Some v
  then v
  else (seqst.(initSt).(MState.regs) !!! 0%fin) reg.

Definition read_byte_seq_state_flag (seqst : seq_state) (pa : pa) : bv 8 * bool :=
  if (seqst.(mem) !! pa) is Some v
  then (v, true)
  else (seqst.(initSt).(MState.memory) pa, false).

Definition read_byte_seq_state (seqst : seq_state) (pa : pa) : bv 8 :=
  fst (read_byte_seq_state_flag seqst pa).

Definition read_mem_seq_state (n : N) (pa : pa) (seqst : seq_state) : bv (8 * n) :=
  pa_range pa (N.to_nat n) |$> read_byte_seq_state seqst |> bv_of_bytes (8 * n).

Definition read_mem_seq_state_flag (n : N) (pa : pa) (seqst : seq_state)
  : bv (8 * n) * bool :=
  let bf := pa_range pa (N.to_nat n) |$> read_byte_seq_state_flag seqst in
  let '(bytes, flags) := split bf in
    (bv_of_bytes (8 * n) bytes, existsb id flags).

Fixpoint write_mem_seq_state (pa : pa) (bytes : list (bv 8)) : seqmon unit :=
  if bytes is byte :: bytes
  then
    msetv (lookup pa ∘ mem) (Some byte);;
    write_mem_seq_state (Arch.pa_addZ pa 1) bytes
  else mret ().

(** Combines a gmap with a registerMap to a new registerMap that was updated
    with the values from the gmap *)
Definition seq_state_to_init_regs (regs_map : gmap reg regval)
  (regs_vec : vec registerMap 1) : vec registerMap 1 :=
  [# (λ reg, if (regs_map !! reg) is Some v then v else (regs_vec !!! 0%fin) reg)].

(** Combines a gmap with a memoryMap to a new memoryMap that was updated with the
    values from the gmap *)
Definition seq_state_to_init_mem (mem_map : gmap pa (bv 8)) (mem : memoryMap)
  : memoryMap :=
  λ pa, if (mem_map !! pa) is Some v then v else mem pa.

(** Turn a seq_state into an MState.init by updating the initial state with the
    gmaps for registers and memory *)
Definition seq_state_to_init (seqs : seq_state) : MState.init 1 :=
  {| MState.state :=
      {| MState.memory :=
          seq_state_to_init_mem seqs.(mem) seqs.(initSt).(MState.memory);
         MState.regs :=
          seq_state_to_init_regs seqs.(regs) seqs.(initSt).(MState.regs) |};
     MState.termCond := seqs.(initSt).(MState.termCond) |}.

(** This is the effect handler for the outcome effect in the sequential model *)
Definition sequential_model_outcome T (call : outcome deps T) : seqmon T :=
  match call with
  | RegRead reg racc => mget (read_reg_seq_state reg)
  | RegWrite reg racc deps val =>
    if regs_whitelist is Some rwl
    then if bool_decide (reg ∈ rwl)
      then msetv (lookup reg ∘ regs) (Some val)
      else mthrow "Write to illegal register"
    else msetv (lookup reg ∘ regs) (Some val)
  | MemRead n rr =>
    if is_ifetch rr.(ReadReq.access_kind) || is_ttw rr.(ReadReq.access_kind)
    then
      '(read, flag) ← mget (read_mem_seq_state_flag n rr.(ReadReq.pa));
      if (flag : bool)
      then mthrow "iFetch or TTW read from modified memory"
      else mret (inl (read, None))
    else
      read ← mget (read_mem_seq_state n rr.(ReadReq.pa));
      mret (inl (read, None))
  | MemWrite n wr =>
    write_mem_seq_state wr.(WriteReq.pa) (wr.(WriteReq.value) |> bv_to_bytes 8);;
    mret (inl true)
  | InstrAnnounce _ => mret ()
  | BranchAnnounce _ deps => mret ()
  | Barrier _ => mret ()
  | CacheOp _ _ => mret ()
  | TlbOp _ _ => mret ()
  | TakeException _ => mthrow "Taking exception is not supported"
  | ReturnException _ => mret ()
  | GenericFail s => mthrow ("Instruction failure: " ++ s)%string
  end.

(** Run instructions until a final state has been reached or fuel is depleted *)
Fixpoint sequential_model_seqmon (fuel : nat) (isem : iMon deps unit)
  : seqmon (MState.final 1) :=
  if fuel is S fuel
  then
    FMon.cinterp sequential_model_outcome isem;;
    st ← mget seq_state_to_init;
    if MState.finalize st is Some final
    then mret final
    else sequential_model_seqmon fuel isem
  else mthrow "Out of fuel".

(** Run the model on given initial MState and an initially blank sequential state.
    The sequential state gets discarded and only the final state is returned *)
Definition sequential_model_exec (fuel : nat) (isem : iMon deps unit)
  (initSt : MState.init 1) : Exec.t string (MState.final 1) :=
  '(_, fs) ← sequential_model_seqmon fuel isem
             {| initSt := initSt; regs := ∅; mem := ∅ |};
  mret fs.

(** Top-level one-threaded sequential model function that takes fuel (guaranteed
    termination) and an instruction monad, and returns a computational set of
    all possible final states. *)
Definition sequential_modelc (fuel : nat) (isem : iMon deps unit) : (Model.c ∅) :=
  λ n,
  match n with
  | 1 => λ initSt : MState.init 1,
           Listset
            (sequential_model_exec fuel isem initSt
             |> Exec.to_result_list
             |$> Model.Res.from_result)
  | _ => λ _, mret (Model.Res.Error "Exptected one thread")
  end.

End Seq.
