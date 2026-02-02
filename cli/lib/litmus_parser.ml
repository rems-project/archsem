(** Litmus test TOML parser.

    Parses TOML files describing litmus tests with the following structure:
    - [[registers]]: Initial register state per thread
    - [[memory]]: Initial memory contents
    - [[termCond]]: Termination conditions per thread (typically PC values)
    - [[outcome]]: Expected observable/unobservable outcomes *)

open Archsem

(** {1 Types} *)

(** A requirement specifies an expected register value with equality or inequality. *)
type requirement =
  | Eq of RegVal.gen
  | Neq of RegVal.gen

(** A condition maps thread IDs to lists of register requirements. *)
type cond = (int * (Reg.t * requirement) list) list

(** An outcome specifies whether a condition is observable or unobservable.
    - Observable: Interesting relaxed behavior the test wants to capture
    - Unobservable: Relaxed behavior the test does not expect to occur *)
type outcome =
  | Observable of cond
  | Unobservable of cond

(** {1 TOML Helpers} *)

let get_int = function
  | Otoml.TomlInteger i -> i
  | _ -> failwith "Expected integer"

let get_list = function
  | Otoml.TomlArray l | Otoml.TomlTableArray l -> l
  | _ -> failwith "Expected list"

let get_pairs = function
  | Otoml.TomlTable pairs | Otoml.TomlInlineTable pairs -> pairs
  | _ -> failwith "Expected table"

(** {1 Register Parsing} *)

(** Parse a register name string (e.g., "X0", "R1", "PSTATE") into a Reg.t *)
let parse_reg_name name =
  match Reg.of_string name with
  | Some r -> Some r
  | None -> if name = "PSTATE" then Some Reg.pstate else None

(** Recursively parse a TOML value into RegVal.gen.
    Handles integers, strings, and nested structs. *)
let rec parse_value = function
  | Otoml.TomlInteger i -> RegVal.Number (Z.of_int i)
  | Otoml.TomlString s -> RegVal.String s
  | Otoml.TomlTable t | Otoml.TomlInlineTable t ->
    RegVal.Struct (List.map (fun (k, v) -> (k, parse_value v)) t)
  | _ -> failwith "Unsupported value type"

(** Parse a requirement from TOML.
    Supports two formats:
    - Simple value: X0 = 1 (implies equality)
    - Explicit op: X0 = \{ op = "eq", val = 1 \} or \{ op = "ne", val = 1 \} *)
let parse_requirement toml =
  let pairs = get_pairs toml in
  match List.assoc_opt "op" pairs, List.assoc_opt "val" pairs with
  | Some (Otoml.TomlString "eq"), Some v -> Eq (parse_value v)
  | Some (Otoml.TomlString "ne"), Some v -> Neq (parse_value v)
  | Some (Otoml.TomlString op), _ -> failwith ("Unknown op: " ^ op)
  | _ -> Eq (parse_value toml)

(** Parse a register key-value pair into (Reg.t, requirement) option.
    Returns None if the key is not a valid register name. *)
let parse_register name toml =
  parse_reg_name name |> Option.map (fun reg -> (reg, parse_requirement toml))

(** Parse a table of register assignments into a list of (Reg.t, requirement). *)
let parse_reg_table toml =
  get_pairs toml |> List.filter_map (fun (k, v) -> parse_register k v)

(** {1 Section Parsing} *)

(** Parse [[registers]] section into initial register maps (one per thread). *)
let parse_registers toml =
  Otoml.find toml get_list ["registers"]
  |> List.map (fun t ->
       parse_reg_table t |> List.fold_left (fun rm (reg, req) ->
         match req with
         | Eq v -> RegMap.insert (RegVal.of_gen reg v |> Result.get_ok) rm
         | Neq _ -> failwith "Neq not supported in initial state"
       ) RegMap.empty)

(** Parse [[memory]] section into initial memory map.
    Each memory block has: base address, size, optional step, and data.
    Data can be a single integer or an array of values. *)
let parse_memory toml =
  Otoml.find toml get_list ["memory"]
  |> List.fold_left (fun mm table ->
       match table with
       | Otoml.TomlTable _ ->
         let base = Otoml.find table get_int ["base"] in
         let size = Otoml.find table get_int ["size"] in
         let step = Otoml.find_opt table get_int ["step"] in
         (match Otoml.find table (fun x -> x) ["data"] with
          | Otoml.TomlArray data_list ->
            let n = List.length data_list in
            let step = Option.value step ~default:(if n > 0 then size / n else 0) in
            List.fold_left (fun (addr, mm) v ->
              (addr + step, MemMap.inserti addr step (get_int v) mm)
            ) (base, mm) data_list |> snd
          | Otoml.TomlInteger v -> MemMap.inserti base size v mm
          | _ -> failwith "Invalid memory data format")
       | _ -> mm
     ) MemMap.empty

(** Parse [[termCond]] section into termination condition checkers.
    Returns a list of functions (one per thread) that check if termination
    conditions are met given the current register map. *)
let parse_termCond num_threads toml =
  let tables = Otoml.find toml get_list ["termCond"] |> List.map parse_reg_table in
  if List.length tables <> num_threads then
    failwith "termCond count must match thread count";
  tables |> List.map (fun regs rm ->
    List.for_all (fun (reg, req) ->
      match RegMap.get_opt reg rm, req with
      | Some rv, Eq exp -> RegVal.to_gen rv = exp
      | Some rv, Neq exp -> RegVal.to_gen rv <> exp
      | None, _ -> false
    ) regs)

(** {1 Outcome Parsing} *)

(** Parse a condition block mapping thread IDs to register requirements. *)
let parse_cond toml =
  get_pairs toml |> List.filter_map (fun (tid_str, regs) ->
    match int_of_string_opt tid_str with
    | None -> failwith ("Invalid thread ID: " ^ tid_str)
    | Some tid -> Some (tid, parse_reg_table regs))

(** Parse all [[outcome]] blocks from the TOML file. *)
let parse_outcomes toml =
  Otoml.find toml get_list ["outcome"] |> List.filter_map (fun node ->
    match node with
    | Otoml.TomlTable pairs | Otoml.TomlInlineTable pairs ->
      (match List.assoc_opt "observable" pairs, List.assoc_opt "unobservable" pairs with
       | Some v, None -> Some (Observable (parse_cond v))
       | None, Some v -> Some (Unobservable (parse_cond v))
       | Some _, Some _ -> failwith "Cannot have both observable and unobservable"
       | None, None -> failwith "Outcome must have observable or unobservable")
    | _ -> None)
