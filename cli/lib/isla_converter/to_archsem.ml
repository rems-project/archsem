(** Archsem TOML output generation.

    Emits memory, registers, termination conditions, and outcomes. *)

(** Merged memory entry for adjacent updates *)
type merged_mem = {
  base: Z.t;
  step: int option;
  size: int;
  values: Z.t list;
  comment: string;
}

let starts_with prefix s =
  String.length s >= String.length prefix &&
  String.sub s 0 (String.length prefix) = prefix

let normalize_reg r = Str.global_replace (Str.regexp "^X") "R" r

(** Deduplicate memory updates by address (later DSL statements override earlier) *)
let dedup_mem_updates updates =
  let tbl = Hashtbl.create 16 in
  List.iter (fun (u: Page_tables.mem_update) ->
    let key = Z.to_string u.addr in
    if not (Hashtbl.mem tbl key) then Hashtbl.add tbl key u
  ) updates;
  Hashtbl.fold (fun _ u acc -> u :: acc) tbl []

(** Merge adjacent memory updates into single entries *)
let merge_mem_updates updates =
  let sorted = List.sort (fun a b -> Z.compare a.Page_tables.addr b.Page_tables.addr) updates in
  let rec merge acc current = function
    | [] -> List.rev (match current with None -> acc | Some m -> m :: acc)
    | u :: rest ->
        match current with
        | None ->
            let m = { base = u.Page_tables.addr; step = None; size = u.Page_tables.size;
                      values = [u.Page_tables.data]; comment = u.Page_tables.comment } in
            merge acc (Some m) rest
        | Some m ->
            let expected = Z.add m.base (Z.of_int (List.length m.values * m.size)) in
            let step_ok = match m.step with None -> true | Some s -> s = m.size in
            if Z.equal u.Page_tables.addr expected && u.Page_tables.size = m.size && step_ok then
              merge acc (Some { m with step = Some m.size; values = m.values @ [u.Page_tables.data] }) rest
            else
              let new_m = { base = u.Page_tables.addr; step = None; size = u.Page_tables.size;
                            values = [u.Page_tables.data]; comment = u.Page_tables.comment } in
              merge (m :: acc) (Some new_m) rest
  in
  merge [] None sorted

let should_show_comment c =
  c = "Initial Data" || starts_with "Code" c || starts_with "Section" c

(** Write [[memory]] block *)
let memory out (m: merged_mem) =
  let comment_str = if should_show_comment m.comment then " # " ^ m.comment else "" in
  match m.values with
  | [single] ->
      Printf.fprintf out "[[memory]]%s\nbase = 0x%s\nsize = %d\ndata = 0x%s\n\n"
        comment_str (Z.format "%x" m.base) m.size (Z.format "%x" single)
  | multiple ->
      let data_str = "[" ^ String.concat ", " (List.map (fun d -> "0x" ^ Z.format "%x" d) multiple) ^ "]" in
      Printf.fprintf out "[[memory]]%s\nbase = 0x%s\nstep = %d\nsize = %d\ndata = %s\n\n"
        comment_str (Z.format "%x" m.base) m.size (m.size * List.length multiple) data_str

(** Write [[memory]] block for code/section *)
let code out label pa size instructions =
  let data_str = "[" ^ String.concat ", " (List.map (Printf.sprintf "0x%x") instructions) ^ "]" in
  Printf.fprintf out "[[memory]] # %s (PA=0x%s)\nbase = 0x%s\nsize = %d\ndata = %s\n\n"
    label (Z.format "%x" pa) (Z.format "%x" pa) (Z.to_int size) data_str

let is_el1_test name =
  try Str.search_forward (Str.regexp_case_fold "EL1") name 0 >= 0
  with Not_found -> false

(** Evaluate register value from TOML *)
let eval_reg_value v =
  match v with
  | Otoml.TomlString s ->
      (match Hashtbl.find_opt Symbols.symbols s with
       | Some addr -> "0x" ^ Z.format "%x" addr
       | None ->
           try "0x" ^ Z.format "%x" (Evaluator.eval (Evaluator.parse_expr s))
           with _ -> "0x0")
  | Otoml.TomlInteger i -> string_of_int i
  | _ -> "0x0"

(** Evaluate PSTATE field value *)
let eval_pstate_value v =
  match v with
  | Otoml.TomlString s ->
      if starts_with "0b" s then s
      else Printf.sprintf "0b%02d" (Z.to_int (Evaluator.eval (Evaluator.parse_expr s)))
  | Otoml.TomlInteger i -> Printf.sprintf "0b%02d" i
  | _ -> "0b00"

(** Write [[registers]] block *)
let registers out thread va root_table test_name ~translation_enabled =
  let parsed_names = ref [] in
  let pstate_fields = ref [] in

  let parsed_regs = List.filter_map (fun (r, v) ->
    let norm_r = normalize_reg r in
    parsed_names := norm_r :: !parsed_names;
    if starts_with "PSTATE." r then begin
      let field = String.sub r 7 (String.length r - 7) in
      pstate_fields := (field, eval_pstate_value v) :: !pstate_fields;
      None
    end else if r = "PSTATE" then
      Some (Printf.sprintf "%s = %s" r (eval_reg_value v))
    else
      Some (Printf.sprintf "%s = %s" norm_r (eval_reg_value v))
  ) thread.Types.reset_regs in

  let sys_regs = [
    ("SCTLR_EL1", if translation_enabled then "0x1" else "0x0");
    ("TCR_EL1", "0x0"); ("ID_AA64MMFR1_EL1", "0x0");
    ("TTBR0_EL1", Printf.sprintf "0x%s" (Z.format "%x" root_table));
    ("ESR_EL1", "0x0"); ("ELR_EL1", "0x0"); ("SPSR_EL1", "0x0");
    ("FAR_EL1", "0x0"); ("VBAR_EL1", "0x0")
  ] |> List.filter (fun (n, _) -> not (List.mem n !parsed_names))
    |> List.map (fun (n, v) -> Printf.sprintf "%s = %s" n v) in

  let pstate =
    if List.mem "PSTATE" !parsed_names then []
    else if !pstate_fields <> [] then
      let el = try List.assoc "EL" !pstate_fields with Not_found -> "0b00" in
      let default_sp = "0b0" in  (* SP=0 so exceptions vector to offset 0x000 *)
      let sp = try List.assoc "SP" !pstate_fields with Not_found -> default_sp in
      [Printf.sprintf "PSTATE = { \"EL\" = %s, \"SP\" = %s }" el sp]
    else if is_el1_test test_name then
      ["PSTATE = { \"EL\" = 0b01, \"SP\" = 0b0 }"]
    else
      ["PSTATE = { \"EL\" = 0b00, \"SP\" = 0b0 }"]
  in

  let default_regs =
    let rec range i acc =
      if i > 30 then acc
      else
        let rn = "R" ^ string_of_int i in
        if List.mem rn !parsed_names then range (i + 1) acc
        else range (i + 1) (Printf.sprintf "%s = 0x0" rn :: acc)
    in range 0 []
  in

  Printf.fprintf out "[[registers]] # %s\n_PC = 0x%s\n%s\n\n"
    thread.Types.tid (Z.format "%x" va)
    (String.concat "\n" (parsed_regs @ sys_regs @ pstate @ default_regs))

let ends_with_eret instructions =
  match List.rev instructions with
  | last :: _ -> last = Constants.eret_opcode
  | [] -> false

(** Compute termination PCs for a thread *)
let compute_term_pcs tid va size sections =
  let main_end = Z.add va size in
  let handler_prefix = "thread" ^ tid in
  let handler_ends = List.filter_map (fun s ->
    if starts_with handler_prefix s.Types.sec_name &&
       String.contains s.Types.sec_name '_' &&
       not (ends_with_eret s.Types.sec_instructions)
    then Some (Z.add s.Types.sec_addr s.Types.sec_size)
    else None
  ) sections in
  main_end :: handler_ends

(** Write [[termCond]] block *)
let term_cond out tid va size sections =
  match compute_term_pcs tid va size sections with
  | [pc] ->
      Printf.fprintf out "[[termCond]] # %s\n_PC = 0x%s\n\n" tid (Z.format "%x" pc)
  | pcs ->
      let strs = List.map (fun pc -> "0x" ^ Z.format "%x" pc) pcs in
      Printf.fprintf out "[[termCond]] # %s\n_PC = [%s]\n\n" tid (String.concat ", " strs)

(** Resolve symbol to physical address *)
let resolve_symbol symbol =
  match Hashtbl.find_opt Symbols.symbols symbol with
  | Some addr -> Some addr
  | None ->
      List.find_map (fun (name, _, pa_opt) ->
        if name = symbol then
          Option.bind pa_opt (Hashtbl.find_opt Symbols.symbols)
        else None
      ) !Symbols.va_mappings

(** Write [[final]] blocks *)
let outcomes out toml =
  match Otoml.find_opt toml (fun x -> x) ["final"] with
  | Some (Otoml.TomlTable t) ->
      let expect = match List.assoc_opt "expect" t with
        | Some (Otoml.TomlString s) -> s | _ -> "sat" in
      (match List.assoc_opt "assertion" t with
       | Some (Otoml.TomlString s) ->
           let s = String.trim s in
           if s = "true" || s = "" then
             Printf.fprintf out "# No outcome assertion (trivial test)\n\n"
           else begin
             let is_assertion, parsed = Outcomes.parse_assertion s (expect = "sat") in
             let prefix = if is_assertion then "assertion" else "negation" in
             if parsed = [] then
               Printf.fprintf out "# Warning: No outcomes parsed from: %s\n\n" s
             else
               List.iter (fun (outcome: Outcomes.outcome) ->
                 Printf.fprintf out "[[final]]\n";
                 (* Group register assertions by thread *)
                 let grouped = Hashtbl.create 5 in
                 List.iter (fun (tid, reg, value, is_eq) ->
                   let existing = try Hashtbl.find grouped tid with Not_found -> [] in
                   Hashtbl.replace grouped tid ((reg, value, is_eq) :: existing)
                 ) outcome.reg_asserts;

                 let reg_parts = ref [] in
                 Hashtbl.iter (fun tid regs ->
                   let content = String.concat ", " (List.map (fun (r, v, is_eq) ->
                     if is_eq then Printf.sprintf "%s = 0x%s" r (Z.format "%x" v)
                     else Printf.sprintf "%s = { op = \"ne\", val = 0x%s }" r (Z.format "%x" v)
                   ) (List.rev regs)) in
                   reg_parts := Printf.sprintf "\"%s\" = { %s }" tid content :: !reg_parts
                 ) grouped;
                 let reg_str = String.concat ", " (List.rev !reg_parts) in

                 let mem_parts = List.filter_map (fun (sym, value, is_eq) ->
                   match resolve_symbol sym with
                   | Some addr ->
                       let op = if is_eq then "" else ", op = \"ne\"" in
                       Some (Printf.sprintf "{ addr = 0x%s, value = 0x%s, size = 8%s }"
                         (Z.format "%x" addr) (Z.format "%x" value) op)
                   | None ->
                       Printf.fprintf out "# Warning: symbol '%s' not resolved\n" sym;
                       None
                 ) outcome.mem_asserts in
                 let mem_str = if mem_parts = [] then ""
                   else "[" ^ String.concat ", " mem_parts ^ "]" in

                 (* Emit warning for register-to-register constraints *)
                 if outcome.reg_reg_asserts <> [] then
                   List.iter (fun (t1, r1, t2, r2, is_eq) ->
                     let op = if is_eq then "=" else "!=" in
                     Printf.fprintf out "# Note: cross-thread register constraint: %s:%s %s %s:%s\n"
                       t1 r1 op t2 r2
                   ) outcome.reg_reg_asserts;

                 (match reg_str, mem_str with
                  | "", "" -> Printf.fprintf out "%s = {}\n" prefix
                  | r, "" -> Printf.fprintf out "%s = { regs = { %s } }\n" prefix r
                  | "", m -> Printf.fprintf out "%s = { mem = %s }\n" prefix m
                  | r, m -> Printf.fprintf out "%s = { regs = { %s }, mem = %s }\n" prefix r m);
                 Printf.fprintf out "\n"
               ) parsed
           end
       | _ -> Printf.fprintf out "# No outcome assertion\n\n")
  | _ -> Printf.fprintf out "# No outcome assertion\n\n"
