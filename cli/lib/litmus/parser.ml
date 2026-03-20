(** Litmus test TOML parser.

    Parses TOML files describing litmus tests:
    - [[registers]]: Initial register state per thread
    - [[memory]]: Initial memory contents
    - [[termCond]]: Termination conditions per thread (typically PC values)
    - [[outcome]]: Expected observable/unobservable final condition

    Parsing path: TOML -> Testrepr.t *)

module RegValGen = Archsem.RegValGen

(** {1 TOML Helpers} *)

let toml_type_name : Otoml.t -> string = function
  | TomlInteger _ -> "integer"
  | TomlFloat _ -> "float"
  | TomlString _ -> "string"
  | TomlBoolean _ -> "boolean"
  | TomlArray _ -> "array"
  | TomlTable _ -> "table"
  | TomlInlineTable _ -> "inline table"
  | TomlTableArray _ -> "table array"
  | _ -> "unknown"

(** {1 TOML -> Testrepr.t} *)

(** Convert a TOML value to RegValGen.t *)
let rec toml_to_gen : Otoml.t -> RegValGen.t = function
  | TomlInteger i -> Number (Z.of_int i)
  | TomlString s -> String s
  | TomlArray l -> Array (List.map toml_to_gen l)
  | TomlTable t | TomlInlineTable t ->
    Struct (List.map (fun (k, v) -> (k, toml_to_gen v)) t)
  | v -> Error.raise_error Parser "unsupported register value type: %s" (toml_type_name v)

(** Parse [[registers]] into register lists with string keys *)
let parse_test_registers toml =
  let parse_regs = Otoml.get_table_values toml_to_gen in
  Otoml.find toml (Otoml.get_array parse_regs) ["registers"]

(** Parse [[memory]] into abstract memory blocks *)
let parse_test_memory toml : Testrepr.memory_block list =
  let parse_memory_block (table : Otoml.t) : Testrepr.memory_block =
    let _ = Otoml.get_table table in (* <- for error message *)
    let addr = Otoml.find table Otoml.get_integer ["addr"] in
    let values = Otoml.find table (Otoml.get_array ~strict:false Otoml.get_integer) ["data"] in
    let n = List.length values in
    let step = Otoml.find table Otoml.get_integer ["step"] in
    if step <= 0 then Error.raise_error Parser "memory block step must be positive";
    let data = Bytes.create (n * step) in
    List.iteri (fun i v ->
        for j = 0 to step - 1 do
          Bytes.set data (i * step + j) (Char.chr ((v lsr (j * 8)) land 0xFF))
        done
      ) values;
    let sym = Otoml.find_opt table Otoml.get_string ["sym"] in
    let kind = Otoml.find_opt table Otoml.get_string ["kind"]
      |> Option.fold ~none:Testrepr.Data ~some:Testrepr.memory_kind_of_string
    in
    if kind = Code && sym <> None then
      Error.raise_error_ctx Parser ~ctx:"memory" "code blocks must not have sym";
    { addr; step; data; sym; kind }
  in
  Otoml.find toml (Otoml.get_array parse_memory_block) ["memory"]

(** Parse [[termCond]] into term cond lists with string keys *)
let parse_test_termcond toml : (string * RegValGen.t) list list =
  Otoml.find toml
    (Otoml.get_array (Otoml.get_table_values toml_to_gen))
    ["termCond"]

(** {2 Register final condition parsing} *)

(** Parse a requirement from TOML into Testrepr.reg_requirement *)
let parse_reg_requirement (toml : Otoml.t) : Testrepr.reg_requirement =
  match toml with
  | TomlTable pairs | TomlInlineTable pairs ->
    (match List.assoc_opt "op" pairs, List.assoc_opt "val" pairs with
     | Some (TomlString "eq"), Some v -> Testrepr.ReqEq (toml_to_gen v)
     | Some (TomlString "ne"), Some v -> Testrepr.ReqNe (toml_to_gen v)
     | Some (TomlString op), _ -> Error.raise_error_ctx Parser ~ctx:"outcome" "unknown requirement op: %s" op
     | _ -> Testrepr.ReqEq (toml_to_gen toml))
  | _ -> Testrepr.ReqEq (toml_to_gen toml)

(** Parse a condition block into thread conditions with string keys *)
let parse_reg_cond toml : (int * (string * Testrepr.reg_requirement) list) list =
  let regs_table =
    match Otoml.find_opt toml Otoml.get_table ["regs"] with
    | Some regs_table -> regs_table
    | None -> Otoml.get_table toml
  in
  regs_table |> List.filter_map (fun (tid_str, regs) ->
    match int_of_string_opt tid_str with
    | None -> None
    | Some tid ->
      let reqs = Otoml.get_table_values parse_reg_requirement regs in
      Some (tid, reqs))

(** {2 Memory final condition parsing} *)

(** Parse all [[outcome]] blocks into final conditions *)
let parse_mem_requirement (toml : Otoml.t) : Testrepr.mem_requirement =
  match toml with
  | TomlTable pairs | TomlInlineTable pairs ->
    (match List.assoc_opt "op" pairs, List.assoc_opt "val" pairs with
     | Some (TomlString "eq"), Some v ->
       MemEq (Z.of_int @@ Otoml.get_integer v)
     | Some (TomlString "ne"), Some v ->
       MemNe (Z.of_int @@ Otoml.get_integer v)
     | _, _ ->
       Error.raise_error_ctx Parser ~ctx:"outcome.mem" "unknown memory requirement: %s"
                 (Otoml.Printer.to_string toml))
  | _ -> MemEq (Z.of_int @@ Otoml.get_integer toml)

let parse_mem_entry mem sym toml : Testrepr.mem_cond =
  let block =
    try Testrepr.mem_by_sym sym mem
    with Not_found ->
      Error.raise_error_ctx Parser ~ctx:("outcome.mem." ^ sym)
        "not found in memory blocks"
  in
  let req = parse_mem_requirement toml in
  { sym;addr=block.addr;size=Testrepr.block_size block;req }

let parse_mem_conds mem toml : Testrepr.mem_cond list =
  let parse_mem_cond toml =
      Otoml.get_table toml |>
      List.map (fun (sym, v) -> parse_mem_entry mem sym v)
  in
  Otoml.find_or ~default:[] toml parse_mem_cond ["mem"]

let parse_test_finals mem toml : Testrepr.final_cond list =
  let parse_test_final toml =
    let parse_with_mem toml =
      let regs = parse_reg_cond toml in
      let mem = parse_mem_conds mem toml in
      (regs, mem)
    in
    match Otoml.find_opt toml parse_with_mem ["observable"],
          Otoml.find_opt toml parse_with_mem ["unobservable"] with
    | Some (regs, mem), None -> Testrepr.Observable (regs, mem)
    | None, Some (regs, mem) -> Testrepr.Unobservable (regs, mem)
    | Some _, Some _ -> Error.raise_error_ctx Parser ~ctx:"outcome" "cannot have both observable and unobservable"
    | None, None -> Error.raise_error_ctx Parser ~ctx:"outcome" "must have observable or unobservable key"
  in
  Otoml.find toml (Otoml.get_array parse_test_final) ["outcome"]

let resolve_mem_conds memory (mcs : Testrepr.mem_cond list) =
  let sym_table =
    List.filter_map
      (fun (block : Testrepr.memory_block) ->
        Option.map (fun sym -> (sym, (block.addr, block.step))) block.sym)
      memory
  in
  List.map
    (fun (mc : Testrepr.mem_cond) ->
      let addr, size =
        match List.assoc_opt mc.sym sym_table with
        | Some (addr, step) ->
          (addr, if mc.size = 0 then step else mc.size)
        | None -> Error.raise_error_ctx Parser ~ctx:("outcome.mem." ^ mc.sym) "unknown memory symbol"
      in
      { mc with addr; size })
    mcs

let parse_to_testrepr : Otoml.t -> Testrepr.t =
 fun toml ->
  let memory = parse_test_memory toml in
  {
    Testrepr.arch = Otoml.find toml Otoml.get_string ["arch"];
    name = Otoml.find toml Otoml.get_string ["name"];
    registers = parse_test_registers toml;
    memory;
    term_cond = parse_test_termcond toml;
    finals = parse_test_finals memory toml;
  }
