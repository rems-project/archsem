(* Tiny model (sail-tiny-arm) *)
module ArchTiny = ArmInst.ArmTiny.Arch
module TMTiny = ArmInst.ArmTM
module ASTiny = TMTiny.Coq_archState
module SeqModelTiny = ArmInst.ArmSeqModel

module RegTiny = struct

  type t = ArchTiny.reg

  let of_string = ArchTiny.reg_of_string

  let to_string = Armv9_types.string_of_register

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

module RegValTiny = struct

  type t = ArchTiny.reg * Obj.t

  include Reggenval

  let of_gen reg g : (t, string) result =
    match ArchTiny.reg_type_of_gen reg g with
    | Ok rv -> Ok (reg, rv)
    | Error s -> Error s

  let reg (reg, _) = reg

  let to_gen (reg, rv) = ArchTiny.reg_type_to_gen reg rv

end

module RegMapTiny = struct

  type t = TMTiny.registerMap

  let empty = Gmap.GEmpty

  let insert (reg, rv) rm = TMTiny.reg_insert reg rv rm

  let insertZ reg rv rm =
    match RegValTiny.of_gen reg (Number rv) with
    | Ok rv -> insert rv rm
    | Error s -> raise (Failure s)

  let inserti reg rv rm = insertZ reg (Z.of_int rv) rm

  let delete reg rm = TMTiny.reg_delete reg rm

  let get_opt reg rm : RegValTiny.t option =
    match TMTiny.reg_lookup reg rm with
    | Some rv -> Some (reg, rv)
    | None -> None

  let get reg rm : RegValTiny.t = get_opt reg rm |> Stdlib.Option.get

  let getZ reg rm : Z.t =
    match RegValTiny.to_gen (get reg rm) with
    | Number z -> z
    | _ ->
      raise
        (Failure (Printf.sprintf "Register %s was not a number" (RegTiny.to_string reg)))

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


module MemMapTiny = struct

  type t = TMTiny.memoryMap

  let empty = Gmap.GEmpty

  let insert addr size data =
    TMTiny.mem_insert (Z.of_int addr) (Z.of_int size) (Z.extract data 0 (8 * size))

  let inserti addr size data = insert addr size (Z.of_int data)

  let insert_bytes = TMTiny.mem_insert_bytes

end

module ArchStateTiny = struct

  type t = ASTiny.t

  let make regs memory : t =
    {regs; memory; address_space = Armv9_types.PAS_NonSecure}

  let regs (st : t) = st.regs

  let reg i (st : t) = List.nth (st.regs) i

  let num_thread st = List.length (regs st)

  let mem (st : t) = st.memory
end

type termCondTiny = (RegMapTiny.t -> bool) list

let termCondTiny_to_coq (term : termCondTiny) tid rm =
  let tc = List.nth term (Z.to_int tid) in
  tc rm

type empty = |

module ArchModelTiny = struct

  module Res : sig
    type 'flag t =
      | FinalState of ArchStateTiny.t
      | Flagged of 'flag
      | Error of string
  end = TMTiny.Coq_archModel.Res

  type 'a t = (* fuel *) int -> termCondTiny -> ArchStateTiny.t -> 'a Res.t list

end


let seqTiny_model fuel term initState =
  if List.length term != 1 then
    raise (Failure
             "termination condition list must be of size 1 for sequential model");
    SeqModelTiny.sequential_modelc None (Z.of_int fuel)
      (ArmInst.sail_tiny_arm_sem true) (Z.of_int 1)
      (termCondTiny_to_coq term) initState
  |> Obj.magic

let umPromTiny_model fuel term initState =
  UMPromising.coq_UMPromising_pf (ArmInst.sail_tiny_arm_sem true) (Z.of_int fuel)
    (ArchStateTiny.num_thread initState |> Z.of_int) (termCondTiny_to_coq term) initState
  |> Obj.magic

let vmPromTiny_model fuel term initState =
  VMPromising.coq_VMPromising_pf (ArmInst.sail_tiny_arm_sem true) (Z.of_int fuel)
    (ArchStateTiny.num_thread initState |> Z.of_int) (termCondTiny_to_coq term) initState
  |> Obj.magic

(* Full sail-arm model support - primary Arm model *)
module Arch = ArmInst.Arm.Arch
module ArchExtra = ArmInst.Arm.ArchExtra
module TM = ArmInst.ArmTM
module AS = TM.Coq_archState
module SeqModel = ArmInst.ArmSeqModel

module Reg = struct
  type t = Arch.reg

  let of_string = Arch.reg_of_string

  let to_string = Armv9_types.string_of_register

  (* External PC register used by the model *)
  let pc : t = Armv9_types.R_bitvector_64 Armv9_types.PC

  (* Internal _PC register used by sail-arm's fetch_and_execute *)
  let internal_pc : t = Armv9_types.R_bitvector_64 Armv9_types.Coq__PC

  let r i : t = Armv9_types.R_bitvector_64 (
    match i with
    | 0 -> Armv9_types.R0
    | 1 -> Armv9_types.R1
    | 2 -> Armv9_types.R2
    | 3 -> Armv9_types.R3
    | 4 -> Armv9_types.R4
    | 5 -> Armv9_types.R5
    | 6 -> Armv9_types.R6
    | 7 -> Armv9_types.R7
    | 8 -> Armv9_types.R8
    | 9 -> Armv9_types.R9
    | 10 -> Armv9_types.R10
    | _ -> raise (Invalid_argument (Printf.sprintf "R%i doesn't exist" i))
  )

  let sctlr i : t = Armv9_types.R_bitvector_64 (
    match i with
    | 1 -> Armv9_types.SCTLR_EL1
    | 2 -> Armv9_types.SCTLR_EL2
    | 3 -> Armv9_types.SCTLR_EL3
    | _ -> raise (Invalid_argument (Printf.sprintf "SCTLR_EL%i doesn't exist" i))
  )

  let pstate : t = Armv9_types.R_ProcState
end

module RegVal = struct
  type t = Arch.reg * Obj.t

  include Reggenval

  let of_gen reg g : (t, string) result =
    match ArchExtra.reg_type_of_gen reg g with
    | Ok rv -> Ok (reg, rv)
    | Error s -> Error s

  let reg (reg, _) = reg

  let to_gen (reg, rv) = ArchExtra.reg_type_to_gen reg rv
end

module RegMap = struct
  type t = TM.registerMap

  let empty = Gmap.GEmpty

  (** Insert a register with its default (inhabitant) value *)
  let insert_default reg rm =
    let default_val = Armv9_types.coq_Inhabited_register_values reg in
    TM.reg_insert reg default_val rm

  (** Create a register map with all sail-arm registers initialized to defaults.
      This includes all 448+ registers needed by the full ARM model. *)
  let with_all_defaults () =
    let open Armv9_types in
    let rm = ref empty in
    (* Helper to add all registers from a list *)
    let add_regs wrap lst =
      List.iter (fun (_, r) -> rm := insert_default (wrap r) !rm) lst
    in
    (* Add registers from each type category *)
    add_regs (fun _ -> R_BranchType) register_BranchType_list;
    add_regs (fun _ -> R_OpType) register_OpType_list;
    add_regs (fun _ -> R_ProcState) register_ProcState_list;
    add_regs (fun r -> R_Signal r) register_Signal_list;
    add_regs (fun _ -> R_TMState) register_TMState_list;
    add_regs (fun _ -> R___InstrEnc) register___InstrEnc_list;
    add_regs (fun r -> R_bitvector_1 r) register_bitvector_1_list;
    add_regs (fun r -> R_bitvector_128 r) register_bitvector_128_list;
    add_regs (fun r -> R_bitvector_16 r) register_bitvector_16_list;
    add_regs (fun r -> R_bitvector_2 r) register_bitvector_2_list;
    add_regs (fun _ -> R_bitvector_24) register_bitvector_24_list;
    add_regs (fun _ -> R_bitvector_256) register_bitvector_256_list;
    add_regs (fun _ -> R_bitvector_3) register_bitvector_3_list;
    add_regs (fun r -> R_bitvector_32 r) register_bitvector_32_list;
    add_regs (fun r -> R_bitvector_4 r) register_bitvector_4_list;
    add_regs (fun _ -> R_bitvector_512) register_bitvector_512_list;
    add_regs (fun r -> R_bitvector_56 r) register_bitvector_56_list;
    add_regs (fun r -> R_bitvector_64 r) register_bitvector_64_list;
    add_regs (fun r -> R_bitvector_8 r) register_bitvector_8_list;
    add_regs (fun _ -> R_bitvector_88) register_bitvector_88_list;
    add_regs (fun r -> R_bool r) register_bool_list;
    add_regs (fun r -> R_int r) register_int_list;
    add_regs (fun r -> R_option_InterruptID r) register_option_InterruptID_list;
    add_regs (fun _ -> R_option_bitvector_32) register_option_bitvector_32_list;
    add_regs (fun _ -> R_vector_16_bitvector_256) register_vector_16_bitvector_256_list;
    add_regs (fun r -> R_vector_16_bitvector_32 r) register_vector_16_bitvector_32_list;
    add_regs (fun r -> R_vector_16_bitvector_64 r) register_vector_16_bitvector_64_list;
    add_regs (fun _ -> R_vector_16_bool) register_vector_16_bool_list;
    add_regs (fun _ -> R_vector_256_bitvector_2048) register_vector_256_bitvector_2048_list;
    add_regs (fun _ -> R_vector_259_bool) register_vector_259_bool_list;
    add_regs (fun r -> R_vector_31_bitvector_32 r) register_vector_31_bitvector_32_list;
    add_regs (fun _ -> R_vector_31_bitvector_64) register_vector_31_bitvector_64_list;
    add_regs (fun _ -> R_vector_31_bool) register_vector_31_bool_list;
    add_regs (fun _ -> R_vector_31_int) register_vector_31_int_list;
    add_regs (fun _ -> R_vector_32_bitvector_2048) register_vector_32_bitvector_2048_list;
    add_regs (fun r -> R_vector_32_bitvector_64 r) register_vector_32_bitvector_64_list;
    add_regs (fun r -> R_vector_32_bool r) register_vector_32_bool_list;
    add_regs (fun _ -> R_vector_32_int) register_vector_32_int_list;
    add_regs (fun r -> R_vector_4_bitvector_32 r) register_vector_4_bitvector_32_list;
    add_regs (fun r -> R_vector_4_bitvector_64 r) register_vector_4_bitvector_64_list;
    add_regs (fun _ -> R_vector_5_bitvector_64) register_vector_5_bitvector_64_list;
    add_regs (fun r -> R_vector_64_bitvector_64 r) register_vector_64_bitvector_64_list;
    add_regs (fun _ -> R_vector_64_bitvector_8) register_vector_64_bitvector_8_list;
    add_regs (fun r -> R_vector_7_bitvector_64 r) register_vector_7_bitvector_64_list;
    (* Add common configuration registers for instruction execution *)
    let rm = !rm in
    (* Override ALL R_bool registers to false.  The extracted bool_inhabited
       = true, so every R_bool (including SPESampleInFlight, BTypeCompatible,
       FEAT_*_IMPLEMENTED, etc.) defaults to true.  Most boolean flags should
       start as false; the FeatureImpl vector is set separately below. *)
    let rm = List.fold_left (fun rm (_, r) ->
      TM.reg_insert (R_bool r) (Obj.magic false) rm
    ) rm register_bool_list in
    (* Helper for inserting integer values *)
    let set_int reg value rm =
      match ArchExtra.reg_type_of_gen reg (Reggenval.Number (Z.of_int value)) with
      | Ok rv -> TM.reg_insert reg rv rm
      | Error s -> failwith s
    in
    (* Int registers *)
    let rm = set_int (R_int Coq___supported_pa_size) 52 rm in
    let rm = set_int (R_int SEE) 0 rm in
    (* SME/SVE vector length registers - must be valid VL (128-2048, multiple of 128) *)
    let rm = set_int (R_int Coq___max_implemented_smeveclen) 512 rm in
    let rm = set_int (R_int Coq___max_implemented_sveveclen) 512 rm in
    (* Bitvector registers *)
    let rm = set_int (R_bitvector_64 SCTLR_EL1) 0 rm in
    let rm = set_int (R_bitvector_64 SCTLR_EL2) 0 rm in
    let rm = set_int (R_bitvector_64 SCTLR_EL3) 0 rm in
    let rm = set_int (R_bitvector_64 HCR_EL2) 0 rm in
    let rm = set_int (R_bitvector_64 SCR_EL3) 1 rm in
    (* FeatureImpl: start with all features enabled, then disable extensions
       that assert on unconfigured system registers during instruction execution
       (e.g. SPE asserts StatisticalProfilingEnabled, RME asserts GPC state). *)
    let disabled_features =
      let open Armv9_types in
      List.map (fun f -> Z.to_int (num_of_Feature f))
        [ FEAT_SPE; FEAT_SPEv1p1; FEAT_SPEv1p2; FEAT_SPEv1p3; FEAT_SPEv1p4;
          FEAT_SPE_CRR; FEAT_SPE_FDS;
          FEAT_RME;
          FEAT_SME; FEAT_SME2; FEAT_SME2p1; FEAT_SME_FA64; FEAT_SME_F64F64;
          FEAT_SME_F16F16; FEAT_SME_I16I64;
          FEAT_TME;
          FEAT_TRBE; FEAT_TRBE_EXT; FEAT_TRBE_MPAM;
          FEAT_BRBE; FEAT_BRBEv1p1;
        ]
    in
    let n_259 = Z.of_int 259 in
    let feat_impl = Values.vec_init_fn n_259 (fun i ->
      not (List.mem (Z.to_int i) disabled_features)
    ) in
    let rm = TM.reg_insert R_vector_259_bool (Obj.magic feat_impl) rm in
    (* Fix TSTATE: The default Inhabited Z = 1, which sets TMState_depth = 1,
       making the model think it's in an active TME transaction.
       Override with depth = 0 to indicate no transaction. *)
    let fixed_tmstate = { Armv9_types.dummy_TMState with
      Armv9_types.coq_TMState_depth = Z.zero } in
    let rm = TM.reg_insert R_TMState (Obj.magic fixed_tmstate) rm in
    rm

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
    {regs; memory; address_space = Armv9_types.PAS_NonSecure}

  let regs (st : t) = st.regs

  let reg i (st : t) = List.nth (st.regs) i

  let num_thread st = List.length (regs st)

  let mem (st : t) = st.memory
end

type termCond = (RegMap.t -> bool) list

let termCond_to_coq (term : termCond) tid rm =
  let tc = List.nth term (Z.to_int tid) in
  tc rm

module ArchModel = struct
  module Res : sig
    type 'flag t =
      | FinalState of ArchState.t
      | Flagged of 'flag
      | Error of string
  end = TM.Coq_archModel.Res

  type 'a t = (* fuel *) int -> termCond -> ArchState.t -> 'a Res.t list
end

let seq_model fuel term initState =
  if List.length term != 1 then
    raise (Failure
             "termination condition list must be of size 1 for sequential model");
    SeqModel.sequential_modelc None (Z.of_int fuel)
      (ArmInst.sail_arm_sem false) (Z.of_int 1)
      (termCond_to_coq term) initState
  |> Obj.magic

let umProm_model fuel term initState =
  UMPromising.coq_UMPromising_pf (ArmInst.sail_arm_sem false) (Z.of_int fuel)
    (ArchState.num_thread initState |> Z.of_int) (termCond_to_coq term) initState
  |> Obj.magic

let vmProm_model fuel term initState =
  VMPromising.coq_VMPromising_pf (ArmInst.sail_arm_sem false) (Z.of_int fuel)
    (ArchState.num_thread initState |> Z.of_int) (termCond_to_coq term) initState
  |> Obj.magic
