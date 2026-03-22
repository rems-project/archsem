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

type mem_requirement =
  | MemEq of Z.t
  | MemNe of Z.t

type thread_cond = int * (string * reg_requirement) list

type mem_cond = {
  sym : string;
  addr : int;
  size : int;
  req : mem_requirement;
}

type final_cond =
  | Observable of thread_cond list * mem_cond list
  | Unobservable of thread_cond list * mem_cond list

(** {1 Test} *)

type t = {
  arch : string;
  name : string;
  registers : (string * Archsem.RegValGen.t) list list;
  memory : memory_block list;
  term_cond : (string * Archsem.RegValGen.t) list list;
  finals : final_cond list;
}


(** {1 Helper functions} *)

let block_size (mb : memory_block) : int = Bytes.length mb.data

let mem_by_sym (sym : string) mem =
  match List.find_opt (fun (mb : memory_block) -> mb.sym = Some sym) mem with
  | Some mb -> mb
  | None -> raise Not_found
