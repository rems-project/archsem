open Archsem

let get_int = function
  | Otoml.TomlInteger i -> i
  | _ -> failwith "Expected an integer"

let get_list = function
  | Otoml.TomlArray l -> l
  | Otoml.TomlTableArray l -> l
  | _ -> failwith "Expected a list"

let parse_reg_key k =
  match Reg.of_string k with
  | Some r -> Some r
  | None ->
    if k = "PSTATE" then Some Reg.pstate
    else None

let parse_reg_value v =
  match v with
  | Otoml.TomlInteger i -> RegVal.Number (Z.of_int i)
  | Otoml.TomlString s -> RegVal.String s
  | Otoml.TomlTable t | Otoml.TomlInlineTable t ->
    let fields = List.map (fun (k, v) ->
      match v with
      | Otoml.TomlInteger i -> (k, RegVal.Number (Z.of_int i))
      | Otoml.TomlString s -> (k, RegVal.String s)
      | _ -> failwith ("Unsupported struct field type in register value: " ^ k)
    ) t in
    RegVal.Struct fields
  | _ -> failwith "Unsupported register value type"

(* Constraints *)
type requirement =
  | Eq of RegVal.gen
  | Neq of RegVal.gen

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
         | Some (Otoml.TomlString op), _ -> failwith ("Unknown operator: " ^ op)
         (* No op/val keys - treat as struct value (e.g., PSTATE = { EL = 0, SP = 0 }) *)
         | _ -> Eq (parse_reg_value v))
      (* Simple values: treat as equality requirement *)
      | Otoml.TomlInteger _ | Otoml.TomlString _ -> Eq (parse_reg_value v)
      (* Unsupported types *)
      | _ -> failwith ("Unsupported value type for register " ^ k)
    in
    Some (reg, req)
  | None -> None

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

let parse_registers (toml : Otoml.t) : RegMap.t list =
  let register_tables = Otoml.find toml get_list ["registers"] in
  let regvals = parse_register_tables register_tables in
  List.map (fun table ->
    List.fold_left (fun regmap (reg, rv) ->
      match rv with
      | Eq v -> RegMap.insert (RegVal.of_gen reg v |> Result.get_ok) regmap
      | Neq _ -> failwith "Neq not supported in init"
    ) RegMap.empty table
  ) regvals

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
      | _ -> failwith "Unsupported data format in memory section")
    | _ -> memmap
  ) MemMap.empty memory_tables

let parse_state (toml : Otoml.t) : ArchState.t =
  let reg_maps = parse_registers toml in
  let mem_map = parse_memory toml in
  ArchState.make reg_maps mem_map

let parse_termCond (num_threads : int) (toml : Otoml.t) : termCond =
  let term_tables = Otoml.find toml get_list ["termCond"] in
  let terms = parse_register_tables term_tables in
  if num_threads != List.length terms then
    failwith "TermCond table does not match number of threads"
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

type cond = (int * (Reg.t * requirement) list) list

type outcome =
  | Allowed of cond
  | Enforced of cond

let parse_cond (toml : Otoml.t) : cond =
  match toml with
    | Otoml.TomlTable pairs | Otoml.TomlInlineTable pairs ->
      List.filter_map (fun (tid_s, regs_toml) ->
        try
          let tid = int_of_string tid_s in
          let reg_conds =
            match regs_toml with
            | Otoml.TomlTable pairs | Otoml.TomlInlineTable pairs ->
              List.filter_map (
                fun (rk, rv) -> parse_register rk rv
              ) pairs
            | _ -> failwith "Unsupported register value type"
          in
          Some (tid, reg_conds)
        with Failure _ -> failwith ("Invalid thread ID (expected integer): " ^ tid_s)
      ) pairs
    | _ -> failwith "Unsupported register value type"

let parse_outcome (pairs : (string * Otoml.t) list) : outcome =
  let has_allowed = List.exists (fun (k, _) -> k = "allowed") pairs in
  let has_enforced = List.exists (fun (k, _) -> k = "enforced") pairs in
  if has_allowed && has_enforced then
    failwith "Outcome block cannot contain both 'allowed' and 'enforced'";
  match List.find_opt (fun (k, _) -> k = "allowed" || k = "enforced") pairs with
  | Some (k, v) ->
    let cond = parse_cond v in
    if k = "allowed" then Allowed cond else Enforced cond
  | None -> failwith "Outcome block must contain 'allowed' or 'enforced'"

let parse_outcomes (toml : Otoml.t) : outcome list =
  let outcome_tables = Otoml.find toml get_list ["outcome"] in
  List.filter_map (fun node ->
    match node with
    | Otoml.TomlTable pairs | Otoml.TomlInlineTable pairs ->
      Some (parse_outcome pairs)
    | _ -> None
  ) outcome_tables
