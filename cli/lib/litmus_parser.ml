(** Litmus test TOML parser.

    Parses TOML files describing litmus tests with the following structure:
    - [[registers]]: Initial register state per thread
    - [[memory]]: Initial memory contents
    - [[termCond]]: Termination conditions per thread (typically PC values)
    - [[final]]: Expected assertion/negation final conditions *)

open Archsem


(** {1 Types} *)

(** A requirement specifies an expected register value with equality or inequality. *)
type requirement =
  | Eq of RegVal.gen
  | Neq of RegVal.gen

(** A condition maps thread IDs to lists of register requirements. *)
type cond = (int * (Reg.t * requirement) list) list

(** A final condition specifies whether a state is asserted or negated.
    - Assertion: Expected reachable final state
    - Negation: Final state expected to be unreachable *)
type outcome =
  | Assertion of cond
  | Negation of cond


(** {1 TOML Helpers} *)

let get_int = function
  | Otoml.TomlInteger i -> i
  | _ -> failwith "Expected integer"

let get_list = function
  | Otoml.TomlArray l | Otoml.TomlTableArray l -> l
  | _ -> failwith "Expected list"

let get_table = function
  | Otoml.TomlTable table | Otoml.TomlInlineTable table -> table
  | _ -> failwith "Expected table"


(** {1 Register Parsing} *)

(** Parse a register name string (e.g., "X0", "R1", "PSTATE") into a Reg.t *)
let parse_reg_name name =
  match Reg.of_string name with
  | Some r -> r
  | None -> failwith ("Unrecognized register name: " ^ name)

(** Recursively parse a TOML value into RegVal.gen.
    Handles integers, strings, and nested structs. *)
let rec parse_reg_val = function
  | Otoml.TomlInteger i -> RegVal.Number (Z.of_int i)
  | Otoml.TomlString s -> RegVal.String s
  | Otoml.TomlTable t | Otoml.TomlInlineTable t ->
    RegVal.Struct (List.map (fun (k, v) -> (k, parse_reg_val v)) t)
  | _ -> failwith "Unsupported value type"

(** Parse a register key-value pair into (Reg.t, RegVal.gen) *)
let parse_register name toml =
  (parse_reg_name name, parse_reg_val toml)

(** Parse a register TOML table into a list of (Reg.t, RegVal.gen) *)
let parse_reg_table toml =
  get_table toml |> List.map (fun (k, v) -> parse_register k v)


(** {1 Register Requirements Parsing} *)

(** Parse a requirement from TOML.
    Supports two formats:
    - Simple value: X0 = 1 (implies equality)
    - Explicit op: X0 = \{ op = "eq", val = 1 \} or \{ op = "ne", val = 1 \} *)
let parse_requirement toml =
  match toml with
  | Otoml.TomlTable pairs | Otoml.TomlInlineTable pairs ->
    (match List.assoc_opt "op" pairs, List.assoc_opt "val" pairs with
     | Some (Otoml.TomlString "eq"), Some v -> Eq (parse_reg_val v)
     | Some (Otoml.TomlString "ne"), Some v -> Neq (parse_reg_val v)
     | Some (Otoml.TomlString op), _ -> failwith ("Unknown op: " ^ op)
     | _ -> Eq (parse_reg_val toml))  (* Table without op/val = struct value *)
  | _ -> Eq (parse_reg_val toml)  (* Simple value = equality *)

(** Parse a register key-value pair into (Reg.t, requirement) *)
let parse_reg_req name toml =
  (parse_reg_name name, parse_requirement toml)

(** Parse a table of register requirements into a list of (Reg.t, requirement) *)
let parse_reg_req_table toml =
  get_table toml |> List.map (fun (k, v) -> parse_reg_req k v)


(** {1 Section Parsing} *)

(** Parse [[registers]] section into initial register maps (one per thread).
    Argument must be the top-level TOML value *)
let parse_registers toml =
  Otoml.find toml get_list ["registers"]
  |> List.map (fun t ->
       parse_reg_table t |> List.fold_left (fun rm (reg, rv) ->
         RegMap.insert (RegVal.of_gen reg rv |> Result.get_ok) rm
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
  let tables = Otoml.find toml get_list ["termCond"] |> List.map parse_reg_req_table in
  if List.length tables <> num_threads then
    failwith "termCond count must match thread count";
  tables |> List.map (fun reg_reqs rm ->
    List.for_all (fun (reg, req) ->
      match RegMap.get_opt reg rm, req with
      | Some rv, Eq exp -> Result.get_ok (RegVal.of_gen reg exp) = rv
      | Some rv, Neq exp -> Result.get_ok (RegVal.of_gen reg exp) = rv
      | None, _ ->
        failwith ("Termination condition couldn't find register: " ^
                  (Reg.to_string reg))
    ) reg_reqs)


(** {1 Outcome Parsing} *)

(** Parse a condition block mapping thread IDs to register requirements.
    Supports nested format: { regs = { "0" = { R0 = 0 } }, mem = [...] } *)
let parse_cond toml =
  let pairs = get_table toml in
  (* Look for regs key; if not found, treat whole table as thread->regs mapping *)
  let reg_pairs = match List.assoc_opt "regs" pairs with
    | Some regs_table -> get_table regs_table
    | None -> pairs
  in
  reg_pairs |> List.filter_map (fun (tid_str, regs) ->
    match int_of_string_opt tid_str with
    | None -> None  (* Skip non-thread keys like "mem" *)
    | Some tid -> Some (tid, parse_reg_req_table regs))

(** Parse all [[final]] blocks from the TOML file.
    Returns empty list if no final conditions are specified. *)
let parse_outcomes toml =
  match Otoml.find_opt toml get_list ["final"] with
  | None -> []
  | Some outcomes -> outcomes |> List.filter_map (fun node ->
    match node with
    | Otoml.TomlTable pairs | Otoml.TomlInlineTable pairs ->
      (match List.assoc_opt "assertion" pairs, List.assoc_opt "negation" pairs with
       | Some v, None -> Some (Assertion (parse_cond v))
       | None, Some v -> Some (Negation (parse_cond v))
       | Some _, Some _ -> failwith "Cannot have both assertion and negation"
       | None, None -> failwith "Final block must have assertion or negation")
    | _ -> None)
