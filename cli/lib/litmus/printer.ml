(** Litmus test TOML printer.

    Converts Testrepr.t to TOML via Otoml. *)

(** {1 Value Conversion} *)

let rec gen_to_toml (v : Archsem.RegValGen.t) : Otoml.t =
  match v with
  | Number z -> TomlInteger (Z.to_int z)
  | String s -> TomlString s
  | Array vs -> TomlArray (List.map gen_to_toml vs)
  | Struct fields ->
    TomlInlineTable (List.map (fun (k, field) -> (k, gen_to_toml field)) fields)

let req_to_toml (req : Testrepr.reg_requirement) : Otoml.t =
  match req with
  | ReqEq v -> gen_to_toml v
  | ReqNe v ->
    TomlInlineTable [("op", TomlString "ne"); ("val", gen_to_toml v)]

(** {1 Section Builders} *)

let registers_to_toml regs : Otoml.t =
  TomlTable (List.map (fun (reg, rv) -> (reg, gen_to_toml rv)) regs)

let memory_block_to_toml (block : Testrepr.memory_block) : Otoml.t =
  let step = block.step in
  if step <= 0 then failwith "memory block step must be positive";
  let len = Bytes.length block.data in
  let n = len / step in
  assert (len = n * step);
  let values =
    List.init n (fun i ->
        Bytes.sub_string block.data (i * step) step |> Z.of_bits |> Z.to_int)
  in
  let data_toml : Otoml.t =
    match values with
    | [single] -> Otoml.TomlInteger single
    | multiple -> Otoml.TomlArray (List.map (fun v -> Otoml.TomlInteger v) multiple)
  in
  TomlTable (
    (match block.sym with Some sym -> ["sym", Otoml.TomlString sym] | None -> []) @
    (match block.kind with
     | Testrepr.Data -> []
     | kind -> ["kind", Otoml.TomlString (Testrepr.string_of_memory_kind kind)]) @
    ["addr", Otoml.TomlInteger block.addr;
     "step", Otoml.TomlInteger step;
     "data", data_toml]
  )

let termcond_to_toml regs : Otoml.t =
  TomlTable (List.map (fun (reg, rv) -> (reg, gen_to_toml rv)) regs)

let outcome_to_toml (fc : Testrepr.final_cond) =
  let label, thread_conds =
    match fc with
    | Testrepr.Observable tc -> "observable", tc
    | Testrepr.Unobservable tc -> "unobservable", tc
  in
  let entries = List.map (fun (tid, reqs) ->
    string_of_int tid,
    Otoml.TomlInlineTable
      (List.map (fun (reg, req) -> (reg, req_to_toml req)) reqs)
  ) thread_conds in
  Otoml.TomlTable [label, Otoml.TomlTable entries]

(** {1 Public API} *)

let to_toml (test : Testrepr.t) : Otoml.t =
  TomlTable [
    "arch", TomlString test.arch;
    "name", TomlString test.name;
    "registers", TomlTableArray
      (List.map registers_to_toml test.registers);
    "memory", TomlTableArray
      (List.map memory_block_to_toml test.memory);
    "termCond", TomlTableArray
      (List.map termcond_to_toml test.term_cond);
    "outcome", TomlTableArray
      (List.map outcome_to_toml test.finals);
  ]

let to_string test =
  Otoml.Printer.to_string ~force_table_arrays:true (to_toml test)

let to_file path test =
  let oc = open_out path in
  output_string oc (to_string test);
  close_out oc
