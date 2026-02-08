(* Tiny model (sail-tiny-arm) types *)
module RegTiny : sig
  type t

  val of_string : string -> t option

  val to_string : t -> string

  val pc : t

  val r : int -> t

  val sctlr : int -> t

  val pstate : t
end

module RegValTiny : sig
  type t

  type gen =
    | Number of Z.t
    | String of string
    | Array of gen list
    | Struct of (string * gen) list

  val of_gen : RegTiny.t -> gen -> (t, string) result

  val reg : t -> RegTiny.t

  val to_gen : t -> gen
end

module RegMapTiny : sig
  type t

  val empty : t

  val insert : RegValTiny.t -> t -> t

  val insertZ : RegTiny.t -> Z.t -> t -> t

  val inserti : RegTiny.t -> int -> t -> t

  val delete : RegTiny.t -> t -> t

  val get_opt : RegTiny.t -> t -> RegValTiny.t option

  val get : RegTiny.t -> t -> RegValTiny.t

  val getZ : RegTiny.t -> t -> Z.t

  val geti : RegTiny.t -> t -> int
end

module Byte : sig
  type t

  val of_Z : Z.t -> t

  val of_int : int -> t

  val to_Z : t -> Z.t

  val to_int : t -> int
end

module MemMapTiny : sig
  type t

  val empty : t

  val insert : int -> int -> Z.t -> t -> t
  (** address then size then data (little endian) *)

  val inserti : int -> int -> int -> t -> t

  val insert_bytes : Z.t -> Byte.t list -> t -> t
  (** address then list of bytes *)

end

module ArchStateTiny : sig
  type t

  val make : RegMapTiny.t list -> MemMapTiny.t -> t

  val regs : t -> RegMapTiny.t list

  val reg : int -> t -> RegMapTiny.t

  val mem : t -> MemMapTiny.t
end

type termCondTiny = (RegMapTiny.t -> bool) list

type empty = |

module ArchModelTiny : sig

  module Res : sig
    type 'flag t =
      | FinalState of ArchStateTiny.t
      | Flagged of 'flag
      | Error of string
  end

  type 'a t = (* fuel *) int -> termCondTiny -> ArchStateTiny.t -> 'a Res.t list

end

val seqTiny_model : empty ArchModelTiny.t

val umPromTiny_model : empty ArchModelTiny.t

val vmPromTiny_model : empty ArchModelTiny.t

(* Full sail-arm model types *)
module Reg : sig
  type t

  val of_string : string -> t option

  val to_string : t -> string

  val pc : t

  val internal_pc : t
  (** The internal _PC register used by sail-arm's fetch_and_execute *)

  val r : int -> t

  val sctlr : int -> t

  val pstate : t
end

module RegVal : sig
  type t

  type gen = RegValTiny.gen =
    | Number of Z.t
    | String of string
    | Array of gen list
    | Struct of (string * gen) list

  val of_gen : Reg.t -> gen -> (t, string) result

  val reg : t -> Reg.t

  val to_gen : t -> gen
end

module RegMap : sig
  type t

  val empty : t

  (** Create a register map with all sail-arm registers initialized to defaults *)
  val with_all_defaults : unit -> t

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

  val insert : int -> int -> Z.t -> t -> t

  val inserti : int -> int -> int -> t -> t

  val insert_bytes : Z.t -> Byte.t list -> t -> t
end

module ArchState : sig
  type t

  val make : RegMap.t list -> MemMap.t -> t

  val regs : t -> RegMap.t list

  val reg : int -> t -> RegMap.t

  val mem : t -> MemMap.t
end

type termCond = (RegMap.t -> bool) list

module ArchModel : sig
  module Res : sig
    type 'flag t =
      | FinalState of ArchState.t
      | Flagged of 'flag
      | Error of string
  end

  type 'a t = (* fuel *) int -> termCond -> ArchState.t -> 'a Res.t list
end

val seq_model : empty ArchModel.t

val umProm_model : empty ArchModel.t

val vmProm_model : empty ArchModel.t
