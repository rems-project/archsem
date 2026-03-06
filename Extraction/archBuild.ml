open Utils

module type ArchRequired = sig
  module Arch : Interface.Arch

  include module type of ArchInst.ArchInst (Arch) (struct end)

  val default_address_space : Arch.addr_space
end

module Build (ArchReq : ArchRequired) = struct
  open ArchReq
  open Stdlib

  module Reg = struct
    type t = Arch.reg

    let of_string_opt = Arch.reg_of_string

    let of_string reg =
      match of_string_opt reg with
      | Some r -> r
      | None -> failwith ("Unknown register: " ^ reg)

    let to_string = Arch.pretty_reg

    let pc = Arch.pc_reg
  end

  module RegVal = struct
    type t = Arch.reg * Arch.reg_type

    let of_gen_res reg gen =
      match Arch.reg_type_of_gen reg gen with
      | Ok rv -> Ok (reg, rv)
      | Error s -> Error s

    let of_gen reg gen =
      match Arch.reg_type_of_gen reg gen with
      | Ok rv -> (reg, rv)
      | Error s -> failwith s

    let of_string_gen reg gen =
      let reg = Reg.of_string reg in
      of_gen reg gen

    let reg (reg, _) = reg

    let to_gen (reg, rv) = Arch.reg_type_to_gen reg rv
  end

  module RegMap = struct
    type t = TM.registerMap

    let empty = Gmap.GEmpty

    let insert (reg, rv) rm = TM.reg_insert reg rv rm

    let insertZ reg rv rm = insert (RegVal.of_gen reg (Number rv)) rm

    let inserti reg rv rm = insertZ reg (Z.of_int rv) rm

    let delete reg rm = TM.reg_delete reg rm

    let get_opt reg rm : RegVal.t option =
      match TM.reg_lookup reg rm with Some rv -> Some (reg, rv) | None -> None

    let get reg rm : RegVal.t = get_opt reg rm |> Option.get

    let getZ reg rm : Z.t =
      match RegVal.to_gen (get reg rm) with
      | Number z -> z
      | _ ->
          failwith
            (Printf.sprintf "Register %s was not a number" (Reg.to_string reg))

    let geti reg rm : int = getZ reg rm |> Z.to_int
  end

  module MemMap = struct
    type t = TM.memoryMap

    let empty = Gmap.GEmpty

    let insert addr size data =
      TM.mem_insert (Z.of_int addr) (Z.of_int size) (Z.extract data 0 (8 * size))

    let inserti addr size data = insert addr size (Z.of_int data)

    let rec insertb_sub addr data pos len mm =
      if len = 0 then mm
      else
        let mm =
          TM.mem_insert_byte (Z.of_int addr)
            (Bytes.get data pos |> Char.code |> Z.of_int)
            mm
        in
        insertb_sub (addr + 1) data (pos + 1) (len - 1) mm

    let rec insertb addr data mm = insertb_sub addr data 0 (Bytes.length data) mm

    let rec present addr size mm =
      if size < 0 then true
      else
        Option.is_some (TM.mem_lookup_byte (Z.of_int addr) mm)
        && present (addr + 1) (size - 1) mm

    let lookup_opt addr size mm = TM.mem_lookup (Z.of_int addr) (Z.of_int size) mm

    let lookupi_opt addr size mm = lookup_opt addr size mm |> Option.map Z.to_int

    let lookup addr size mm =
      match lookup_opt addr size mm with Some v -> v | None -> raise Not_found

    let lookupi addr size mm = lookup addr size mm |> Z.to_int

    let lookupb addr size mm =
      let res = Bytes.create size in
      for i = 0 to size - 1 do
        match TM.mem_lookup_byte (Z.of_int addr) mm with
        | None -> raise Not_found
        | Some byte -> Bytes.unsafe_set res i (Obj.magic byte)
      done;
      res

    let lookupb_opt addr size mm =
      try Some (lookupb addr size mm) with Not_found -> None
  end

  module ArchState = struct
    type t = TM.Coq_archState.t

    let make regs memory : t =
      (* {regs; memory; address_space = default_address_space} *)
      {regs; memory; address_space = Obj.magic ()}

    let regs (st : t) = st.regs

    let reg i (st : t) = List.nth st.regs i

    let num_thread st = List.length (regs st)

    let mem (st : t) = st.memory
  end

  type termCond = (RegMap.t -> bool) list

  type iSem = unit Interface.iMon

  module ArchModel = struct
    module Res : sig
      type 'flag t =
        | FinalState of ArchState.t
        | Flagged of 'flag
        | Error of string
    end =
      TM.Coq_archModel.Res

    type 'a t = iSem -> (* fuel *) int -> termCond -> ArchState.t -> 'a Res.t list
  end

  let seq_model isem fuel term initState =
    let termCond_coq tid rm =
      let tc = List.nth term (Z.to_int tid) in
      tc rm
    in
    if List.length term != 1 then
      raise
        (Failure
           "termination condition list must be of size 1 for sequential model"
        );
    SeqModel.sequential_modelc None (Z.of_int fuel) isem (Z.of_int 1) termCond_coq
      initState
    |> Obj.magic
end
