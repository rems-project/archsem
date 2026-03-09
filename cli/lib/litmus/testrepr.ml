(** Abstract archsem test representation.

    Uses plain OCaml types (string for register names, RegValGen.t for values)
    to remain architecture-neutral.  Conversion to arch-specific Coq types
    happens in ToArchState.Make(Arch). *)

(** {1 Memory Types} *)

type memory_kind =
  | Code
  | Data
  | PageTable

let memory_kind_of_string = function
  | "code" -> Code
  | "pagetable" -> PageTable
  | _ -> Data

let string_of_memory_kind = function
  | Code -> "code"
  | Data -> "data"
  | PageTable -> "pagetable"

type memory_block = {
  addr : int;
  step : int;
  data : Bytes.t;
  sym : string option;
  kind : memory_kind;
}

(** {1 Outcome Types} *)

type reg_requirement =
  | ReqEq of Archsem.RegValGen.t
  | ReqNe of Archsem.RegValGen.t

type thread_cond = int * (string * reg_requirement) list

type final_cond =
  | Observable of thread_cond list
  | Unobservable of thread_cond list

(** {1 Test} *)

type t = {
  arch : string;
  name : string;
  registers : (string * Archsem.RegValGen.t) list list;
  memory : memory_block list;
  term_cond : (string * Archsem.RegValGen.t) list list;
  finals : final_cond list;
}
