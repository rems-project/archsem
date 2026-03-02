open Utils

module type ArchRequired = sig

  module Arch : Interface.Arch

  include module type of ArchInst.ArchInst(Arch)(struct end)

  val default_address_space : Arch.addr_space
end


module Build (ArchReq : ArchRequired) = struct
  open ArchReq

  module Reg = struct
    type t = Arch.reg

    let of_string = Arch.reg_of_string

    let to_string = Arch.pretty_reg

    let pc = Arch.pc_reg
  end

  module RegVal = struct
    type t = Arch.reg * Arch.reg_type

    let of_gen reg gen =
      match Arch.reg_type_of_gen reg gen with
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

  module MemMap = struct

    type t = TM.memoryMap

    let empty = Gmap.GEmpty

    let insert addr size data =
      TM.mem_insert (Z.of_int addr) (Z.of_int size) (Z.extract data 0 (8 * size))

    let inserti addr size data = insert addr size (Z.of_int data)

  end

  module ArchState = struct

    type t = TM.Coq_archState.t

    let make regs memory : t =
      (* {regs; memory; address_space = default_address_space} *)
      {regs; memory; address_space = Obj.magic ()}

    let regs (st : t) = st.regs

    let reg i (st : t) = List.nth (st.regs) i

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
    end = TM.Coq_archModel.Res

    type 'a t = iSem -> (* fuel *) int -> termCond -> ArchState.t -> 'a Res.t list

  end

  let seq_model isem fuel term initState =
    let termCond_coq tid rm =
      let tc = List.nth term (Z.to_int tid) in
      tc rm
    in
    if List.length term != 1 then
      raise (Failure
               "termination condition list must be of size 1 for sequential model");
    SeqModel.sequential_modelc None (Z.of_int fuel)
      isem (Z.of_int 1) termCond_coq initState
    |> Obj.magic

end
