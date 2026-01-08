open Archsem

let get_int = function
  | Otoml.TomlInteger i -> i
  | _ -> failwith "[Parser] Expected an integer"

let get_list = function
  | Otoml.TomlArray l -> l
  | Otoml.TomlTableArray l -> l
  | _ -> failwith "[Parser] Expected a list"

(** Parses a register name string (e.g., "X0", "PSTATE") into a Reg.t *)
let parse_reg_key k =
  match Reg.of_string k with
  | Some r -> Some r
  | None ->
    if k = "PSTATE" then Some Reg.pstate
    else None

(** Parses a TOML value into RegVal.gen (handles integers, strings, structs) *)
let parse_reg_value v =
  match v with
  | Otoml.TomlInteger i -> RegVal.Number (Z.of_int i)
  | Otoml.TomlString s -> RegVal.String s
  | Otoml.TomlTable t | Otoml.TomlInlineTable t ->
    let fields = List.map (fun (k, v) ->
      match v with
      | Otoml.TomlInteger i -> (k, RegVal.Number (Z.of_int i))
      | Otoml.TomlString s -> (k, RegVal.String s)
      | _ -> failwith ("[Parser] Unsupported struct field type: " ^ k)
    ) t in
    RegVal.Struct fields
  | _ -> failwith "[Parser] Unsupported register value type"

(* Constraints *)
type requirement =
  | Eq of RegVal.gen
  | Neq of RegVal.gen

(** Parses a register key-value pair into (Reg.t, requirement) with eq/ne support *)
let parse_register (k : string) (v : Otoml.t) : (Reg.t * requirement) option =
  match parse_reg_key k with
  | Some reg ->
    let req = match v with
      (* For outcomes: requires explicit { op = "eq"/"ne", val = ... } *)
      (* For init: if op/val not present, treat as struct value *)
      | Otoml.TomlTable pairs | Otoml.TomlInlineTable pairs ->
        (match List.assoc_opt "op" pairs, List.assoc_opt "val" pairs with
         | Some (Otoml.TomlString "eq"), Some v -> Eq (parse_reg_value v)
         | Some (Otoml.TomlString "ne"), Some v -> Neq (parse_reg_value v)
         | Some (Otoml.TomlString op), _ -> failwith ("[Parser] Unknown operator: " ^ op)
         (* No op/val keys - treat as struct value (e.g., PSTATE = { EL = 0, SP = 0 }) *)
         | _ -> Eq (parse_reg_value v))
      (* Simple values: treat as equality requirement *)
      | Otoml.TomlInteger _ | Otoml.TomlString _ -> Eq (parse_reg_value v)
      (* Unsupported types *)
      | _ -> failwith ("[Parser] Unsupported value type for register: " ^ k)
    in
    Some (reg, req)
  | None -> None

(** Parses [[registers]] or [[termCond]] table arrays into register requirement lists *)
let parse_register_tables (register_tables : Otoml.t list) : ((Reg.t * requirement) list) list =
  List.map (fun table ->
    match table with
    | Otoml.TomlTable pairs | Otoml.TomlInlineTable pairs ->
      List.fold_left (fun regvals (k, v) ->
        match parse_register k v with
        | Some reg -> reg :: regvals
        | None ->
          Printf.printf "Warning: Unknown register %s\n" k;
          regvals
      ) [] pairs
    | _ -> []
  ) register_tables

(** Parses [[registers]] section into initial register maps (one per thread) *)
let parse_registers (toml : Otoml.t) : RegMap.t list =
  let register_tables = Otoml.find toml get_list ["registers"] in
  let regvals = parse_register_tables register_tables in
  List.map (fun table ->
    List.fold_left (fun regmap (reg, rv) ->
      match rv with
      | Eq v -> RegMap.insert (RegVal.of_gen reg v |> Result.get_ok) regmap
      | Neq _ -> failwith "[Config] Neq not supported in init"
    ) RegMap.empty table
  ) regvals

(** Parses [[memory]] section into initial memory map *)
let parse_memory (toml : Otoml.t) : MemMap.t =
  let memory_tables = Otoml.find toml get_list ["memory"] in
  List.fold_left (fun memmap table ->
    match table with
    | Otoml.TomlTable _ -> (
      let base = Otoml.find table get_int ["base"] in
      let step_opt = Otoml.find_opt table get_int ["step"] in
      let size = Otoml.find table get_int ["size"] in
      let data = Otoml.find table (fun x -> x) ["data"] in

      match data with
      | Otoml.TomlArray data_list ->
        let count = List.length data_list in
        let step = Option.value step_opt ~default:(if count > 0 then size / count else 0) in
        List.fold_left (fun (current_addr, current_map) val_toml ->
          let val_int = get_int val_toml in
          (current_addr + step, MemMap.inserti current_addr step val_int current_map)
        ) (base, memmap) data_list |> snd
      | Otoml.TomlInteger val_int ->
        MemMap.inserti base size val_int memmap
      | _ -> failwith "[Parser] Unsupported data format in memory section")
    | _ -> memmap
  ) MemMap.empty memory_tables

(** Parses initial architecture state from [[registers]] and [[memory]] *)
let parse_state (toml : Otoml.t) : ArchState.t =
  let reg_maps = parse_registers toml in
  let mem_map = parse_memory toml in
  ArchState.make reg_maps mem_map

(** Parses [[termCond]] section into termination condition checkers *)
let parse_termCond (num_threads : int) (toml : Otoml.t) : termCond =
  let term_tables = Otoml.find toml get_list ["termCond"] in
  let terms = parse_register_tables term_tables in
  if num_threads != List.length terms then
    failwith "[Config] TermCond table does not match number of threads"
  else
    (* Build a checker function for each thread based on ALL register conditions *)
    List.map (fun table ->
      (* Generate a function that checks all conditions in the table *)
      (fun rm ->
        List.for_all (fun (reg, req) ->
          let reg_val = RegMap.get_opt reg rm in
          match reg_val, req with
          | Some rv, Eq expected ->
            RegVal.to_gen rv = expected
          | Some rv, Neq expected ->
            RegVal.to_gen rv <> expected
          | None, _ ->
            (* Register not found - condition fails *)
            false
        ) table)
    ) terms

(* A single thread's register requirements *)
type reg_cond = (Reg.t * requirement) list

(* Single register assertion for one thread *)
type reg_assertion = int * reg_cond

(* Single memory assertion *)
type mem_assertion = Z.t * int * requirement

type outcome =
  | Allowed of reg_assertion list * mem_assertion list
  | Forbidden of reg_assertion list * mem_assertion list

(** Parses a condition block (thread ID -> register requirements) *)
let parse_cond (toml : Otoml.t) : reg_assertion list =
  match toml with
    | Otoml.TomlTable pairs | Otoml.TomlInlineTable pairs ->
      List.filter_map (fun (tid_s, regs_toml) ->
        (* Skip non-numeric keys like "mem" from "forbidden.mem" *)
        match int_of_string_opt tid_s with
        | Some tid ->
          let reg_conds =
            match regs_toml with
            | Otoml.TomlTable pairs | Otoml.TomlInlineTable pairs ->
              List.filter_map (
                fun (rk, rv) -> parse_register rk rv
              ) pairs
            | _ -> failwith "[Parser] Unsupported register value type"
          in
          Some (tid, reg_conds)
        | None -> None  (* Skip non-integer keys *)
      ) pairs
    | _ -> failwith "[Parser] Unsupported register value type"


(** Parses a single memory assertion block into (addr, size, requirement) *)
let parse_single_mem_assertion (t : (string * Otoml.t) list) : mem_assertion option =
  match List.assoc_opt "addr" t, List.assoc_opt "value" t, List.assoc_opt "size" t with
  | Some (Otoml.TomlInteger addr), Some (Otoml.TomlInteger value), Some (Otoml.TomlInteger size) ->
      Some (Z.of_int addr, size, Eq (Number (Z.of_int value)))
  | Some (Otoml.TomlString addr_hex), Some (Otoml.TomlInteger value), Some (Otoml.TomlInteger size) ->
      (* Handle hex string addresses like "0x21000" *)
      let addr = Z.of_string addr_hex in
      Some (addr, size, Eq (Number (Z.of_int value)))
  (* Support op = "ne" for inequality assertions *)
  | Some addr_toml, Some value_toml, Some (Otoml.TomlInteger size) ->
      let addr = match addr_toml with
        | Otoml.TomlInteger i -> Z.of_int i
        | Otoml.TomlString s -> Z.of_string s
        | _ -> failwith "[Parser] Invalid addr type in memory assertion"
      in
      let (value, req_type) = match List.assoc_opt "op" t with
        | Some (Otoml.TomlString "ne") ->
            (match value_toml with
             | Otoml.TomlInteger v -> (Z.of_int v, fun v -> Neq v)
             | _ -> failwith "[Parser] Invalid value type")
        | _ ->
            (match value_toml with
             | Otoml.TomlInteger v -> (Z.of_int v, fun v -> Eq v)
             | _ -> failwith "[Parser] Invalid value type")
      in
      Some (addr, size, req_type (Number value))
  | _ -> None

(** Parses a single [[outcome]] block into Allowed or Forbidden *)
let parse_outcome (pairs : (string * Otoml.t) list) : outcome =
  let has_allowed = List.exists (fun (k, _) -> k = "allowed") pairs in
  let has_forbidden = List.exists (fun (k, _) -> k = "forbidden") pairs in
  if has_allowed && has_forbidden then
    failwith "[Config] Outcome cannot contain both 'allowed' and 'forbidden'";
  match List.find_opt (fun (k, _) -> k = "allowed" || k = "forbidden") pairs with
  | Some (k, v) ->
    (* Parse register assertions: look for "regs" key, or fall back to parsing directly *)
    let reg_assertions =
      match v with
      | Otoml.TomlTable t | Otoml.TomlInlineTable t ->
          (match List.assoc_opt "regs" t with
           | Some reg_toml -> parse_cond reg_toml  (* New format: allowed.regs = {...} *)
           | None -> parse_cond v)  (* Old format: allowed.0 = {...} directly *)
      | _ -> parse_cond v
    in
    (* Parse memory assertions: look for "mem" key under allowed/forbidden *)
    let mem_assertions =
      match v with
      | Otoml.TomlTable t | Otoml.TomlInlineTable t ->
          (match List.assoc_opt "mem" t with
           | Some (Otoml.TomlArray arr) ->
               (* Array of memory assertions: [{ addr = ..., value = ..., size = ... }, ...] *)
               List.filter_map (fun item ->
                 match item with
                 | Otoml.TomlTable t | Otoml.TomlInlineTable t -> parse_single_mem_assertion t
                 | _ -> None
               ) arr
           | Some (Otoml.TomlTable t) | Some (Otoml.TomlInlineTable t) ->
               (* Single memory assertion: { addr = ..., value = ..., size = ... } *)
               (match parse_single_mem_assertion t with Some a -> [a] | None -> [])
           | _ -> [])
      | _ -> []
    in
    if k = "allowed" then Allowed (reg_assertions, mem_assertions) else Forbidden (reg_assertions, mem_assertions)
  | None -> failwith "[Config] Outcome must contain 'allowed' or 'forbidden'"

(** Parses all [[outcome]] blocks from the TOML file *)
let parse_outcomes (toml : Otoml.t) : outcome list =
  match Otoml.find_opt toml get_list ["outcome"] with
  | Some outcome_tables ->
    List.filter_map (fun node ->
      match node with
      | Otoml.TomlTable pairs | Otoml.TomlInlineTable pairs ->
        Some (parse_outcome pairs)
      | _ -> None
    ) outcome_tables
  | None -> []  (* No outcomes defined - trivial test *)

