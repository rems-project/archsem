open Archsem

let get_int = function
  | Otoml.TomlInteger i -> i
  | _ -> failwith "Expected an integer"

let get_list = function
  | Otoml.TomlArray l -> l
  | Otoml.TomlTableArray l -> l
  | _ -> failwith "Expected a list"

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

let parse_reg_key k =
  match Reg.of_string k with
  | Some r -> Some r
  | None ->
    if k = "PSTATE" then Some Reg.pstate
    else None

let parse_register (k : string) (v : Otoml.t) : (Reg.t * RegVal.gen) option =
  match parse_reg_key k with
  | Some reg -> Some (reg, parse_reg_value v)
  | None -> None

let parse_register_tables (register_tables : Otoml.t list) : ((Reg.t * RegVal.gen) list) list =
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
      RegMap.insert (RegVal.of_gen reg rv |> Result.get_ok) regmap
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
    (* Return non-terminating termCond *)
    failwith "TermCond table does not match number of threads"
  else
    (* Current extraction of termCond only supports a single register check on PC *)
    List.map (fun table ->
      match List.find_opt (fun (r, _) -> r = Reg.pc) table with
      | Some (_, RegVal.Number n) -> (fun pc -> Z.equal pc n)
      | _ -> failwith "TermCond table does not contain a single register check on PC"
    ) terms

let parse_outcomes (toml : Otoml.t) : string * (int * (Reg.t * RegVal.gen) list) list list =
  let outcomes = Otoml.find toml get_list ["outcome"] in

  let kind = ref "allowed" in

  let checks = List.map (fun node ->
    match node with
    | Otoml.TomlTable pairs | Otoml.TomlInlineTable pairs ->
      List.filter_map (fun (k, v) ->
        let current_kind, explicit_tid =
          if k = "allowed" then ("allowed", None)
          else if k = "enforced" then ("enforced", None)
          else if k = "expected" then ("allowed", None)
          else if String.length k > 8 && String.sub k 0 8 = "allowed." then
              ("allowed", Some (String.sub k 8 (String.length k - 8)))
          else if String.length k > 9 && String.sub k 0 9 = "enforced." then
              ("enforced", Some (String.sub k 9 (String.length k - 9)))
          else ("unknown", None)
        in

        if current_kind <> "unknown" then (
          kind := current_kind;
          match explicit_tid with
          | Some tid_s ->
              (* v is the registers table for this tid *)
              (try
                  let tid = int_of_string tid_s in
                  match v with
                  | Otoml.TomlTable reg_pairs | Otoml.TomlInlineTable reg_pairs ->
                      let regs = List.filter_map (fun (rk, rv) -> parse_register rk rv) reg_pairs in
                      Some [(tid, regs)]
                  | _ -> None
              with _ -> None)
          | None ->
              (* v is table of threads: tid -> regs *)
              match v with
              | Otoml.TomlTable threads | Otoml.TomlInlineTable threads ->
                  let thread_checks = List.filter_map (fun (tid_s, regs_toml) ->
                      try
                          let tid = int_of_string tid_s in
                          match regs_toml with
                          | Otoml.TomlTable reg_pairs | Otoml.TomlInlineTable reg_pairs ->
                              let regs = List.filter_map (fun (rk, rv) -> parse_register rk rv) reg_pairs in
                              Some (tid, regs)
                          | _ -> None
                      with Failure _ -> None
                  ) threads in
                  Some thread_checks
              | _ -> None
           ) else None
       ) pairs |> List.flatten
    | _ -> []
  ) outcomes in
  (!kind, checks)
