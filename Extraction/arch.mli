module type Arch = sig
  module Reg : sig
    type t

    val of_string_opt : string -> t option

    val of_string : string -> t

    val to_string : t -> string

    val pc : t
  end

  module RegVal : sig
    type t

    val of_gen_res : Reg.t -> RegValGen.t -> (t, string) result

    val of_gen : Reg.t -> RegValGen.t -> t

    val of_string_gen : string -> RegValGen.t -> t

    val reg : t -> Reg.t

    val to_gen : t -> RegValGen.t
  end

  module RegMap : sig
    type t

    val empty : t

    val insert : RegVal.t -> t -> t

    val insertZ : Reg.t -> Z.t -> t -> t

    val inserti : Reg.t -> int -> t -> t

    val delete : Reg.t -> t -> t

    val get_opt : Reg.t -> t -> RegVal.t option

    val get : Reg.t -> t -> RegVal.t

    val getZ : Reg.t -> t -> Z.t

    val geti : Reg.t -> t -> int
  end

  module MemMap : sig
    type t

    val empty : t

    (** address then size then data (little endian) *)
    val insert : int -> int -> Z.t -> t -> t

    val inserti : int -> int -> int -> t -> t

    val insertb : int -> Bytes.t -> t -> t

    (** Check whether a range of memory is entirely present *)
    val present : int -> int -> t -> bool

    (** little-endian *)
    val lookup_opt : int -> int -> t -> Z.t option

    (** This will crash if the result doesn't fin the integer *)
    val lookupi_opt : int -> int -> t -> int option

    val lookupb_opt : int -> int -> t -> Bytes.t option

    (** little-endian, raise Not_found if not all bytes are set *)
    val lookup : int -> int -> t -> Z.t

    (** This will crash if the result doesn't fin the integer
        raise Not_found if not all bytes are set *)
    val lookupi : int -> int -> t -> int

    (** raise Not_found if not all bytes are set *)
    val lookupb : int -> int -> t -> Bytes.t
  end

  module ArchState : sig
    type t

    val make : RegMap.t list -> MemMap.t -> t

    val regs : t -> RegMap.t list

    val reg : int -> t -> RegMap.t

    val mem : t -> MemMap.t
  end

  type termCond = (RegMap.t -> bool) list

  (** Instruction semantics, opaque for now *)
  type iSem

  module ArchModel : sig
    module Res : sig
      type 'flag t =
        | FinalState of ArchState.t
        | Flagged of 'flag
        | Error of string
    end

    type 'a t = iSem -> (* fuel *) int -> termCond -> ArchState.t -> 'a Res.t list
  end

  val seq_model : Utils.empty ArchModel.t
end
