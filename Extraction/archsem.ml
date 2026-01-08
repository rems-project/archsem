module Arch = ArmInst.Arm.Arch
module TM = ArmInst.ArmTM
module AS = TM.Coq_archState
module SeqModel = ArmInst.ArmSeqModel

module Reg = struct

  type t = Arch.reg

  let of_string = Arch.reg_of_string

  let to_string = System_types.string_of_register

  let pc : t = R_bitvector_64 Coq__PC

  let r i : t =
    match i with
    | 0 -> R_bitvector_64 R0
    | 1 -> R_bitvector_64 R1
    | 2 -> R_bitvector_64 R2
    | 3 -> R_bitvector_64 R3
    | 4 -> R_bitvector_64 R4
    | 5 -> R_bitvector_64 R5
    | 6 -> R_bitvector_64 R6
    | 7 -> R_bitvector_64 R7
    | 8 -> R_bitvector_64 R8
    | 9 -> R_bitvector_64 R9
    | 10 -> R_bitvector_64 R10
    | _ -> raise (Invalid_argument (Printf.sprintf "R%i doesn't exist" i))

  let sctlr i : t =
    match i with
    | 1 -> R_bitvector_64 SCTLR_EL1
    | 2 -> R_bitvector_64 SCTLR_EL2
    | 3 -> R_bitvector_64 SCTLR_EL3
    | _ -> raise (Invalid_argument (Printf.sprintf "SCTLR_EL%i doesn't exist" i))

  let pstate :t = R_ProcState
end

module RegVal = struct

  type t = Arch.reg * Obj.t

  include Reggenval

  let of_gen reg g : (t, string) result =
    match Arch.reg_type_of_gen reg g with
    | Ok rv -> Ok (reg, rv)
    | Error s -> Error s

  let reg (reg, _) = reg

  let to_gen (reg, rv) = Arch.reg_type_to_gen reg rv

end

module RegMap = struct

  type t = TM.registerMap

  let empty = Gmap.GEmpty

  let insert (reg, rv) rm = TM.reg_insert reg rv rm

  let insertZ reg rv rm =
    match RegVal.of_gen reg (Number rv) with
    | Ok rv -> insert rv rm
    | Error s -> raise (Failure s)

  let inserti reg rv rm = insertZ reg (Z.of_int rv) rm

  let delete reg rm = TM.reg_delete reg rm

  let get_opt reg rm : RegVal.t option =
    match TM.reg_lookup reg rm with
    | Some rv -> Some (reg, rv)
    | None -> None

  let get reg rm : RegVal.t = get_opt reg rm |> Stdlib.Option.get

  let getZ reg rm : Z.t =
    match RegVal.to_gen (get reg rm) with
    | Number z -> z
    | _ ->
      raise
        (Failure (Printf.sprintf "Register %s was not a number" (Reg.to_string reg)))

  let geti reg rm : int = getZ reg rm |> Z.to_int
end

module Byte = struct

  (* Must be between 0 and 255 *)
  type t = Z.t

  let of_Z i = Z.extract i 0 8

  let of_int i = of_Z (Z.of_int i)

  let to_Z b = b

  let to_int i = (Obj.magic i)
end


module MemMap = struct

  type t = TM.memoryMap

  let empty = Gmap.GEmpty

  let insert addr size data =
    TM.mem_insert (Z.of_int addr) (Z.of_int size) (Z.extract data 0 (8 * size))

  let inserti addr size data = insert addr size (Z.of_int data)

  let insert_bytes = TM.mem_insert_bytes

end

module ArchState = struct

  type t = AS.t

  let make regs memory : t =
    {regs; memory = memory; final_memory = None; address_space = System_types.PAS_NonSecure}

  let regs (st : t) = st.regs

  let reg i (st : t) = List.nth (st.regs) i

  let num_thread st = List.length (regs st)

  let mem (st : t) = st.memory

  (* Read from final memory state if present, otherwise use initial memory *)
  let mem_read (addr : Z.t) (size : int) (st : t) : RegVal.gen option =
    let memory_to_read = match st.final_memory with
      | Some fm -> fm
      | None -> st.memory
    in
    match TM.mem_read (Z.of_int size) addr memory_to_read with
    | Some bytes ->
        let value = List.fold_left (fun acc b ->
          Z.logor (Z.shift_left acc 8) b
        ) Z.zero bytes in
        Some (RegVal.Number value)
    | None -> None
end

type termCond = (RegMap.t -> bool) list

let termCond_to_coq (term : termCond) tid rm =
  let tc = List.nth term (Z.to_int tid) in
  tc rm

type empty = |

module ArchModel = struct

  module Res : sig
    type 'flag t =
      | FinalState of ArchState.t
      | Flagged of 'flag
      | Error of string
  end = TM.Coq_archModel.Res

  type 'a t = (* fuel *) int -> termCond -> ArchState.t -> 'a Res.t list

  type 'a vmp_t = (* fuel *) int -> (* debug *) bool -> (* mem_strict *) bool -> (* bbm_check *) bool -> termCond -> ArchState.t -> 'a Res.t list

end


let seq_model fuel term initState =
  if List.length term != 1 then
    raise (Failure
             "termination condition list must be of size 1 for sequential model");
    SeqModel.sequential_modelc None (Z.of_int fuel)
      (ArmInst.sail_tiny_arm_sem true) (Z.of_int 1)
      (termCond_to_coq term) initState
  |> Obj.magic

let umProm_model fuel term initState =
  UMPromising.coq_UMPromising_cert_c (ArmInst.sail_tiny_arm_sem true) (Z.of_int fuel)
    (ArchState.num_thread initState |> Z.of_int) (termCond_to_coq term) initState
  |> Obj.magic

let vmProm_model fuel debug mem_strict bbm_check term initState =
  VMPromising.coq_VMPromising_cert_c (ArmInst.sail_tiny_arm_sem true) (Z.of_int fuel)
    debug mem_strict bbm_check (ArchState.num_thread initState |> Z.of_int) (termCond_to_coq term) initState
  |> Obj.magic
