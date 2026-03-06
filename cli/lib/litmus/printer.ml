(** Litmus test TOML printer.

    Converts Spec.t to TOML via Otoml. *)

open Archsem

(** {1 Value Conversion} *)

let rec gen_to_toml = function
  | RegVal.Number z -> Otoml.TomlInteger (Z.to_int z)
  | RegVal.String s -> Otoml.TomlString s
  | RegVal.Array vs -> Otoml.TomlArray (List.map gen_to_toml vs)
  | RegVal.Struct fields ->
    Otoml.TomlInlineTable
      (List.map (fun (k, v) -> (k, gen_to_toml v)) fields)

let req_to_toml = function
  | Spec.ReqEq v -> gen_to_toml v
  | Spec.ReqNe v ->
    Otoml.TomlInlineTable
      [("op", Otoml.TomlString "ne"); ("val", gen_to_toml v)]

(** {1 Section Builders} *)

let registers_to_toml regs =
  Otoml.TomlTable
    (List.map (fun (reg, rv) -> (Reg.to_string reg, gen_to_toml rv)) regs)

let read_le data offset step =
  let v = ref 0 in
  for j = step - 1 downto 0 do
    v := (!v lsl 8) lor (Char.code (Bytes.get data (offset + j)))
  done;
  !v

let memory_block_to_toml (block : Spec.memory_block) =
  let step = block.step in
  let len = Bytes.length block.data in
  let n = if step > 0 then len / step else 0 in
  let values = List.init n (fun i -> read_le block.data (i * step) step) in
  let data_toml = match values with
    | [single] -> Otoml.TomlInteger single
    | multiple ->
      Otoml.TomlArray (List.map (fun v -> Otoml.TomlInteger v) multiple)
  in
  Otoml.TomlTable (
    (match block.name with Some n -> ["name", Otoml.TomlString n] | None -> []) @
    (match block.kind with Some k -> ["kind", Otoml.TomlString (Spec.string_of_memory_kind k)] | None -> []) @
    ["base", Otoml.TomlInteger (Z.to_int block.base);
     "size", Otoml.TomlInteger block.size;
     "step", Otoml.TomlInteger step;
     "data", data_toml])

let termcond_to_toml regs =
  Otoml.TomlTable
    (List.map (fun (reg, rv) -> (Reg.to_string reg, gen_to_toml rv)) regs)

let mem_cond_to_toml (mc : Spec.mem_cond) =
  let default = Config.default_mem_size () in
  match mc.req with
  | Spec.MemEq v when mc.size = default ->
    (mc.sym, Otoml.TomlInteger (Z.to_int v))
  | _ ->
    let pairs =
      (match mc.req with
       | Spec.MemEq v -> [("val", Otoml.TomlInteger (Z.to_int v))]
       | Spec.MemNe v -> [("op", Otoml.TomlString "ne"); ("val", Otoml.TomlInteger (Z.to_int v))])
      @ (if mc.size <> default then [("size", Otoml.TomlInteger mc.size)] else [])
    in
    (mc.sym, Otoml.TomlInlineTable pairs)

let outcome_to_toml (fc : Spec.final_cond) =
  let label, thread_conds, mem_conds = match fc with
    | Spec.Observable (tc, mc) -> "observable", tc, mc
    | Spec.Unobservable (tc, mc) -> "unobservable", tc, mc
  in
  let thread_entries = List.map (fun (tid, reqs) ->
    string_of_int tid,
    Otoml.TomlInlineTable
      (List.map (fun (reg, req) -> (Reg.to_string reg, req_to_toml req)) reqs)
  ) thread_conds in
  let mem_entries = match mem_conds with
    | [] -> []
    | _ -> ["mem", Otoml.TomlInlineTable (List.map mem_cond_to_toml mem_conds)]
  in
  Otoml.TomlTable [label, Otoml.TomlTable (thread_entries @ mem_entries)]

(** {1 Public API} *)

let to_toml (test : Spec.t) =
  Otoml.TomlTable [
    "arch", Otoml.TomlString test.arch;
    "name", Otoml.TomlString test.name;
    "registers", Otoml.TomlTableArray
      (List.map registers_to_toml test.registers);
    "memory", Otoml.TomlTableArray
      (List.map memory_block_to_toml test.memory);
    "termCond", Otoml.TomlTableArray
      (List.map termcond_to_toml test.term_cond);
    "outcome", Otoml.TomlTableArray
      (List.map outcome_to_toml test.finals);
  ]

let to_string test =
  Otoml.Printer.to_string ~force_table_arrays:true (to_toml test)

let to_file path test =
  let oc = open_out path in
  output_string oc (to_string test);
  close_out oc
