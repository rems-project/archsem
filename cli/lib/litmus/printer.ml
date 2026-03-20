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
  | ReqNe v -> TomlInlineTable [("op", TomlString "ne"); ("val", gen_to_toml v)]

(** {1 Section Builders} *)

let registers_to_toml regs : Otoml.t =
  TomlTable (List.map (fun (reg, rv) -> (reg, gen_to_toml rv)) regs)

let memory_block_to_toml (block : Testrepr.memory_block) : Otoml.t =
  let step = block.step in
  if step <= 0 then Error.raise_error Printer "memory block step must be positive";
  let len = Bytes.length block.data in
  let n = len / step in
  assert (len = n * step);
  let values =
    List.init n (fun i ->
      Bytes.sub_string block.data (i * step) step |> Z.of_bits |> Z.to_int
    )
  in
  let data_toml : Otoml.t =
    match values with
    | [single] -> Otoml.TomlInteger single
    | multiple ->
        Otoml.TomlArray (List.map (fun v -> Otoml.TomlInteger v) multiple)
  in
  TomlTable
    (( match block.sym with
       | Some sym -> [("sym", Otoml.TomlString sym)]
       | None -> []
       )
    @ ( match block.kind with
      | Testrepr.Data -> []
      | kind -> [("kind", Otoml.TomlString (Testrepr.string_of_memory_kind kind))]
      )
    @ [ ("addr", Otoml.TomlInteger block.addr);
        ("step", Otoml.TomlInteger step);
        ("data", data_toml)
      ]
    )

let termcond_to_toml regs : Otoml.t =
  TomlTable (List.map (fun (reg, rv) -> (reg, gen_to_toml rv)) regs)

let mem_cond_to_toml default_size (mc : Testrepr.mem_cond) =
  match mc.req with
  | Testrepr.MemEq v when mc.size = default_size ->
      (mc.sym, Otoml.TomlInteger (Z.to_int v))
  | _ ->
      let pairs =
        ( match mc.req with
          | Testrepr.MemEq v -> [("val", Otoml.TomlInteger (Z.to_int v))]
          | Testrepr.MemNe v ->
              [ ("op", Otoml.TomlString "ne");
                ("val", Otoml.TomlInteger (Z.to_int v))
              ]
          )
        @
        if mc.size <> default_size then [("size", Otoml.TomlInteger mc.size)]
        else []
      in
      (mc.sym, Otoml.TomlInlineTable pairs)

let outcome_to_toml (test : Testrepr.t) (fc : Testrepr.final_cond) =
  let (label, thread_conds, mem_conds) =
    match fc with
    | Testrepr.Observable (tc, mc) -> ("observable", tc, mc)
    | Testrepr.Unobservable (tc, mc) -> ("unobservable", tc, mc)
  in
  let thread_entries =
    List.map
      (fun (tid, reqs) ->
         ( string_of_int tid,
           Otoml.TomlInlineTable
             (List.map (fun (reg, req) -> (reg, req_to_toml req)) reqs)
         )
       )
      thread_conds
  in
  let memory_sizes =
    List.filter_map
      (fun (block : Testrepr.memory_block) ->
         Option.map (fun sym -> (sym, block.step)) block.sym
       )
      test.memory
  in
  let mem_entries =
    match mem_conds with
    | [] -> []
    | _ ->
        [ ( "mem",
            Otoml.TomlInlineTable
              (List.map
                 (fun (mc : Testrepr.mem_cond) ->
                    let default_size =
                      match List.assoc_opt mc.sym memory_sizes with
                      | Some size -> size
                      | None -> mc.size
                    in
                    mem_cond_to_toml default_size mc
                  )
                 mem_conds
              )
          )
        ]
  in
  Otoml.TomlTable [(label, Otoml.TomlTable (thread_entries @ mem_entries))]

(** {1 Public API} *)

let to_toml (test : Testrepr.t) : Otoml.t =
  TomlTable
    [ ("arch", TomlString test.arch);
      ("name", TomlString test.name);
      ("registers", TomlTableArray (List.map registers_to_toml test.registers));
      ("memory", TomlTableArray (List.map memory_block_to_toml test.memory));
      ("termCond", TomlTableArray (List.map termcond_to_toml test.term_cond));
      ("outcome", TomlTableArray (List.map (outcome_to_toml test) test.finals))
    ]

let to_string test =
  Otoml.Printer.to_string ~force_table_arrays:true (to_toml test)

let to_file path test =
  try
    let oc = open_out path in
    output_string oc (to_string test);
    close_out oc
  with Sys_error msg -> Error.raise_error_ctx Printer ~ctx:path "%s" msg
