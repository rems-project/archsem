(** Abstract archsem test representation.

    Uses Coq-extracted types (Reg.t, RegVal.gen) for registers
    and plain OCaml types for memory and metadata. *)

open Archsem

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
  base : Z.t;
  size : int;
  step : int;
  data : Bytes.t;
  name : string option;
  kind : memory_kind option;
}

(** {1 Outcome Types} *)

type reg_requirement =
  | ReqEq of RegVal.gen
  | ReqNe of RegVal.gen

type mem_requirement =
  | MemEq of Z.t
  | MemNe of Z.t

type thread_cond = int * (Reg.t * reg_requirement) list

type mem_cond = {
  sym : string;
  addr : Z.t;
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
  registers : (Reg.t * RegVal.gen) list list;
  memory : memory_block list;
  term_cond : (Reg.t * RegVal.gen) list list;
  finals : final_cond list;
}

(** {1 Equality} *)

let reg_requirement_equal a b =
  match a, b with
  | ReqEq x, ReqEq y | ReqNe x, ReqNe y -> x = y
  | _ -> false

let thread_cond_equal (t1, reqs1) (t2, reqs2) =
  t1 = t2 &&
  List.equal (fun (r1, req1) (r2, req2) ->
    r1 = r2 && reg_requirement_equal req1 req2) reqs1 reqs2

let mem_requirement_equal a b =
  match a, b with
  | MemEq x, MemEq y | MemNe x, MemNe y -> Z.equal x y
  | _ -> false

let mem_cond_equal a b =
  a.sym = b.sym && Z.equal a.addr b.addr && a.size = b.size &&
  mem_requirement_equal a.req b.req

let final_cond_equal a b =
  match a, b with
  | Observable (ts1, ms1), Observable (ts2, ms2)
  | Unobservable (ts1, ms1), Unobservable (ts2, ms2) ->
    List.equal thread_cond_equal ts1 ts2 &&
    List.equal mem_cond_equal ms1 ms2
  | _ -> false

let reg_list_equal a b =
  List.equal (fun (r1, v1) (r2, v2) -> r1 = r2 && v1 = v2) a b

let memory_block_equal a b =
  Z.equal a.base b.base && a.size = b.size && a.step = b.step &&
  a.name = b.name && a.kind = b.kind &&
  Bytes.equal a.data b.data

let equal a b =
  a.arch = b.arch && a.name = b.name &&
  List.equal reg_list_equal a.registers b.registers &&
  List.equal memory_block_equal a.memory b.memory &&
  List.equal reg_list_equal a.term_cond b.term_cond &&
  List.equal final_cond_equal a.finals b.finals
