(** Merged memory entry for adjacent updates *)
type merged_update = {
  base: Z.t;
  step: int option;  (* None for single entry *)
  size: int;
  data_list: Z.t list;
  merged_comment: string;
}

(** Deduplicate memory updates by address.
    Since updates are prepended to the list, the FIRST entry for each address
    is from the LAST DSL statement. We want later DSL statements to override
    earlier ones, so we iterate forward (keeping first occurrence). *)
let dedup_updates (updates: Page_tables.mem_update list) : Page_tables.mem_update list =
  let tbl = Hashtbl.create 16 in
  List.iter (fun (u: Page_tables.mem_update) ->
    let key = Z.to_string u.Page_tables.addr in
    if not (Hashtbl.mem tbl key) then Hashtbl.add tbl key u
  ) updates;
  Hashtbl.fold (fun _ u acc -> u :: acc) tbl []

(** Sort memory updates by address *)
let sort_updates (updates: Page_tables.mem_update list) : Page_tables.mem_update list =
  List.sort (fun (a: Page_tables.mem_update) (b: Page_tables.mem_update) -> Z.compare a.Page_tables.addr b.Page_tables.addr) updates

(** Merge adjacent memory updates with same step into single entry *)
let merge_adjacent_updates (updates: Page_tables.mem_update list) : merged_update list =
  let sorted = List.sort (fun (a: Page_tables.mem_update) (b: Page_tables.mem_update) -> Z.compare a.Page_tables.addr b.Page_tables.addr) updates in
  let rec merge acc current = function
    | [] ->
        (match current with
         | None -> List.rev acc
         | Some m -> List.rev (m :: acc))
    | (u: Page_tables.mem_update) :: rest ->
        (match current with
         | None ->
             (* Start new group *)
             let m = { base = u.Page_tables.addr; step = None; size = u.Page_tables.size;
                       data_list = [u.Page_tables.data]; merged_comment = u.Page_tables.comment } in
             merge acc (Some m) rest
         | Some m ->
             let expected_addr = Z.add m.base (Z.of_int ((List.length m.data_list) * m.size)) in
             let step_matches = match m.step with
               | None -> true  (* First pair, any step is ok *)
               | Some s -> s = m.size
             in
             if Z.equal u.Page_tables.addr expected_addr && u.Page_tables.size = m.size && step_matches then
               (* Extend current group *)
               let new_m = { m with
                 step = Some m.size;
                 data_list = m.data_list @ [u.Page_tables.data];
               } in
               merge acc (Some new_m) rest
             else
               (* Start new group *)
               let new_m = { base = u.Page_tables.addr; step = None; size = u.Page_tables.size;
                             data_list = [u.Page_tables.data]; merged_comment = u.Page_tables.comment } in
               merge (m :: acc) (Some new_m) rest)
  in
  merge [] None sorted

(** Check if a comment should be shown (Initial Data, Code, Section only) *)
let should_show_comment comment =
  comment = "Initial Data" ||
  String.length comment >= 4 && String.sub comment 0 4 = "Code" ||
  String.length comment >= 7 && String.sub comment 0 7 = "Section"

(** Emit memory block to output *)
let emit_memory out (m: merged_update) =
  let comment_str = if should_show_comment m.merged_comment then " # " ^ m.merged_comment else "" in
  match m.data_list with
  | [single] ->
      (* Single entry - original format *)
      Printf.fprintf out "[[memory]]%s\nbase = 0x%s\nsize = %d\ndata = 0x%s\n\n"
        comment_str (Z.format "%x" m.base) m.size (Z.format "%x" single)
  | multiple ->
      (* Merged entry - array format with step *)
      let data_str = "[" ^ (String.concat ", " (List.map (fun d -> "0x" ^ Z.format "%x" d) multiple)) ^ "]" in
      let total_size = m.size * (List.length multiple) in
      Printf.fprintf out "[[memory]]%s\nbase = 0x%s\nstep = %d\nsize = %d\ndata = %s\n\n"
        comment_str (Z.format "%x" m.base) m.size total_size data_str

(** Emit code block to output *)
let emit_code out label pa size instructions =
  let data_str = "[" ^ (String.concat ", " (List.map (Printf.sprintf "0x%x") instructions)) ^ "]" in
  Printf.fprintf out "[[memory]] # %s (PA=0x%s)\nbase = 0x%s\nsize = %d\ndata = %s\n\n"
    label (Z.format "%x" pa) (Z.format "%x" pa) (Z.to_int size) data_str

(** Check if test name indicates EL1 execution *)
let is_el1_test name =
  try Str.search_forward (Str.regexp_case_fold "EL1") name 0 >= 0
  with Not_found -> false

(** Emit register block to output.
    translation_enabled: if false, sets SCTLR_EL1=0 (for usermode tests without page tables) *)
let emit_registers out thread va root_table test_name ~translation_enabled =
  let parsed_reg_names = ref [] in
  let pstate_fields = ref [] in  (* Collect PSTATE.* fields *)

  let parsed_regs = List.filter_map (fun (r, v) ->
    (* Normalize X registers to R format for tracking *)
    let norm_r = Str.global_replace (Str.regexp "^X") "R" r in
    parsed_reg_names := norm_r :: !parsed_reg_names;
    (* Handle PSTATE.* fields specially - preserve original format *)
    if String.length r > 7 && String.sub r 0 7 = "PSTATE." then begin
      let field = String.sub r 7 (String.length r - 7) in
      let vs = match v with
        | Otoml.TomlString s ->
            (* Preserve binary format for PSTATE fields *)
            if String.length s >= 2 && String.sub s 0 2 = "0b" then s
            else Printf.sprintf "0b%02d" (Z.to_int (Evaluator.eval (Evaluator.parse_string s)))
        | Otoml.TomlInteger i -> Printf.sprintf "0b%02d" i
        | _ -> "0b00"
      in
      pstate_fields := (field, vs) :: !pstate_fields;
      None  (* Don't include in parsed_regs *)
    end else begin
      let vs = match v with
        | Otoml.TomlString s ->
            (* First check if it's a known symbol (for init section) *)
            (match Hashtbl.find_opt Symbols.symbols s with
             | Some addr -> "0x" ^ (Z.format "%x" addr)
             | None ->
                 (* Try to evaluate as expression *)
                 try "0x" ^ (Z.format "%x" (Evaluator.eval (Evaluator.parse_string s)))
                 with _ -> "0x0")  (* Default to 0 if evaluation fails *)
        | Otoml.TomlInteger i -> string_of_int i
        | _ -> "0x0"
      in
      if r = "PSTATE" then
        Some (Printf.sprintf "%s = %s" r vs)  (* Full PSTATE already formatted *)
      else
        Some (Printf.sprintf "%s = %s" norm_r vs)  (* Use normalized register name *)
    end
  ) thread.Input_parser.reset_regs in

  let sys_regs = [
    ("SCTLR_EL1", if translation_enabled then "0x1" else "0x0");
    ("TCR_EL1", "0x0");
    ("ID_AA64MMFR1_EL1", "0x0");
    ("TTBR0_EL1", Printf.sprintf "0x%s" (Z.format "%x" root_table));
    ("ESR_EL1", "0x0"); ("ELR_EL1", "0x0"); ("SPSR_EL1", "0x0"); ("FAR_EL1", "0x0"); ("VBAR_EL1", "0x0")
  ] |> List.filter (fun (n, _) -> not (List.mem n !parsed_reg_names))
    |> List.map (fun (n, v) -> Printf.sprintf "%s = %s" n v) in

  (* Build PSTATE from fields or use defaults *)
  let pstate =
    if List.mem "PSTATE" !parsed_reg_names then
      []  (* Full PSTATE already in parsed_regs *)
    else if !pstate_fields <> [] then begin
      (* Build PSTATE from individual fields *)
      let el = try List.assoc "EL" !pstate_fields with Not_found -> "0b00" in
      (* Default SP based on EL: EL1 uses SP_EL1 (SP=1), EL0 uses SP_EL0 (SP=0) *)
      let default_sp = if el = "0b01" then "0b1" else "0b0" in
      let sp = try List.assoc "SP" !pstate_fields with Not_found -> default_sp in
      [Printf.sprintf "PSTATE = { \"EL\" = %s, \"SP\" = %s }" el sp]
    end else begin
      (* Default based on test name: if contains "EL1", use EL1 with SP=1 *)
      if is_el1_test test_name then
        ["PSTATE = { \"EL\" = 0b01, \"SP\" = 0b1 }"]
      else
        ["PSTATE = { \"EL\" = 0b00, \"SP\" = 0b0 }"]
    end
  in

  let default_regs =
    let rec range i acc =
      if i > 30 then acc
      else
        let rn = "R" ^ (string_of_int i) in
        if List.mem rn !parsed_reg_names then range (i + 1) acc
        else range (i + 1) ((Printf.sprintf "%s = 0x0" rn) :: acc)
    in range 0 []
  in

  Printf.fprintf out "[[registers]] # %s\n_PC = 0x%s\n%s\n\n"
    thread.Input_parser.tid (Z.format "%x" va)
    (String.concat "\n" (parsed_regs @ sys_regs @ pstate @ default_regs))

(** Check if an instruction list ends with ERET (0xd69f03e0) *)
let ends_with_eret instructions =
  match List.rev instructions with
  | last :: _ -> last = 0xd69f03e0
  | [] -> false

(** Emit termination condition.
    If the thread has an associated exception handler without ERET,
    use the handler's end address as the termination PC. *)
let emit_term_cond out tid va size sections =
  (* Check for handler section matching pattern "thread<tid>_el1_handler" or similar *)
  let handler_pattern = "thread" ^ tid in
  let handler_section = List.find_opt (fun s ->
    String.length s.Input_parser.sec_name >= String.length handler_pattern &&
    String.sub s.Input_parser.sec_name 0 (String.length handler_pattern) = handler_pattern &&
    String.contains s.Input_parser.sec_name '_' &&
    not (ends_with_eret s.Input_parser.sec_instructions)
  ) sections in
  let term_pc = match handler_section with
    | Some s -> Z.add s.Input_parser.sec_addr s.Input_parser.sec_size  (* Handler end PC *)
    | None -> Z.add va size  (* Normal code end PC *)
  in
  Printf.fprintf out "[[termCond]] # %s\n_PC = 0x%s\n\n" tid (Z.format "%x" term_pc)

(** Resolve memory symbol to physical address *)
let resolve_mem_symbol symbol =
  match Hashtbl.find_opt Symbols.symbols symbol with
  | Some addr -> Some addr
  | None ->
    List.find_map (fun (name, _va, pa_name_opt) ->
      if name = symbol then
        match pa_name_opt with
        | Some pa_name -> Hashtbl.find_opt Symbols.symbols pa_name
        | None -> None
      else None
    ) !Symbols.va_mappings

(** Emit outcome assertions using the proper boolean expression parser **)
let emit_outcomes out toml =
  match Otoml.find_opt toml (fun x -> x) ["final"] with
  | Some (Otoml.TomlTable t) ->
    let expect = match List.assoc_opt "expect" t with Some (Otoml.TomlString s) -> s | _ -> "sat" in
    (match List.assoc_opt "assertion" t with
      | Some (Otoml.TomlString s) ->
        let s_clean = String.trim s in
        (* Handle trivial assertions - "true" or empty *)
        if s_clean = "true" || s_clean = "" then
          Printf.fprintf out "# No outcome assertion (trivial test)\n\n"
        else (
          (* Parse the assertion using the proper boolean expression parser *)
          let expect_sat = (expect = "sat") in
          let (is_allowed, outcomes) = Assertion_parser.parse_assertion s_clean expect_sat in
          let prefix = if is_allowed then "allowed" else "forbidden" in

          if outcomes = [] then
            Printf.fprintf out "# Warning: No outcomes parsed from assertion: %s\n\n" s_clean
          else
            List.iter (fun (outcome : Assertion_parser.outcome) ->
              Printf.fprintf out "[[outcome]]\n";

              (* Group register assertions by thread *)
              let grouped = Hashtbl.create 5 in
              List.iter (fun (tid, reg, value, is_eq) ->
                let existing = try Hashtbl.find grouped tid with Not_found -> [] in
                Hashtbl.replace grouped tid ((reg, value, is_eq) :: existing)
              ) outcome.reg_asserts;

              (* Build reg assertions string *)
              let reg_parts = ref [] in
              Hashtbl.iter (fun tid regs ->
                let content = String.concat ", " (List.map (fun (r, v, is_eq) ->
                  if is_eq then
                    Printf.sprintf "%s = %d" r v
                  else
                    Printf.sprintf "%s = { op = \"ne\", val = %d }" r v
                ) (List.rev regs)) in
                reg_parts := Printf.sprintf "\"%s\" = { %s }" tid content :: !reg_parts
              ) grouped;
              let reg_str = if !reg_parts = [] then "" else String.concat ", " (List.rev !reg_parts) in

              (* Build mem assertions string *)
              let mem_parts = List.filter_map (fun (symbol, value, is_eq) ->
                match resolve_mem_symbol symbol with
                | Some addr ->
                  let le_val = Z.shift_left (Z.of_int value) 56 in
                  let op_str = if is_eq then "" else ", op = \"ne\"" in
                  Some (Printf.sprintf "{ addr = 0x%s, value = 0x%s, size = 8%s }"
                    (Z.format "%x" addr) (Z.format "%x" le_val) op_str)
                | None ->
                  Printf.fprintf out "# Warning: symbol '%s' not resolved, skipping memory assertion\n" symbol;
                  None
              ) outcome.mem_asserts in
              let mem_str = if mem_parts = [] then "" else "[" ^ String.concat ", " mem_parts ^ "]" in

              (* Emit combined format *)
              (match (reg_str, mem_str) with
              | ("", "") -> Printf.fprintf out "%s = {}\n" prefix
              | (r, "") -> Printf.fprintf out "%s = { regs = { %s } }\n" prefix r
              | ("", m) -> Printf.fprintf out "%s = { mem = %s }\n" prefix m
              | (r, m) -> Printf.fprintf out "%s = { regs = { %s }, mem = %s }\n" prefix r m);
              Printf.fprintf out "\n"
            ) outcomes
        )
      | _ -> Printf.fprintf out "# No outcome assertion\n\n")
  | _ -> Printf.fprintf out "# No outcome assertion\n\n"
