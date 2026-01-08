open Ast

(** =============================================================================
    TYPES
    ============================================================================= *)

(** Memory update to be emitted in the TOML output *)
type mem_update = { addr: Z.t; data: Z.t; size: int; comment: string }

(** Thread code and register configuration *)
type thread_info = {
  tid: string;
  code_pa: Z.t;
  code_size: Z.t;
  instructions: int list;
  reset_regs: (string * Otoml.t) list;
}

(** Exception handler section *)
type section_info = {
  sec_name: string;
  sec_addr: Z.t;
  sec_size: Z.t;
  sec_instructions: int list;
}

(** Accumulated state during conversion *)
type state = {
  mutable pt_updates: mem_update list;
  mutable has_code_identity: bool;
  root_table: Z.t ref;
}

(** AArch64 L3 Page Descriptor format (4KB granule):
    Bits [1:0]  = 0b11  Valid page descriptor
    Bits [4:2]  = 0b000 AttrIndx (MAIR index 0)
    Bit  [5]    = 0     NS (Non-secure, ignored in EL1&0)
    Bits [7:6]  = 0b01  AP[2:1] (EL0 read/write, EL1 read/write)
    Bits [9:8]  = 0b11  SH (Inner Shareable)
    Bit  [10]   = 1     AF (Access Flag) — must be set
    Bit  [11]   = 0     nG (non-Global)
    Bits [47:12] = PA   Output physical address

    Standard descriptor value: 0x743 = 0b011101000011 (EL0/EL1 R/W)
    With PA: (PA & ~0xFFF) | 0x743 *)
let page_descriptor = 0x743
let page_mask = Z.of_string "0xFFFFFFFFFFFFF000"

(** =============================================================================
    PAGE TABLE INSTALLATION
    ============================================================================= *)

(** Install a page table mapping from VA to target descriptor *)
let rec install_mapping state table_base level va target force_level alias_opt va_sym_opt =
  let shift = match level with 0->39 | 1->30 | 2->21 | 3->12 | _->0 in
  let idx = Z.to_int (Z.logand (Z.shift_right va shift) (Z.of_int 0x1FF)) in
  let entry_addr = Z.add table_base (Z.of_int (idx * 8)) in
  let is_leaf = level = 3 || (match force_level with Some l -> l = level | None -> false) in

  if is_leaf then (
    let desc = match target with
      | TInvalid -> Z.zero
      | TPA p -> Z.logor (Symbols.get_symbol_addr p) (Z.of_int page_descriptor)
      | TTable p_name -> Z.logor (Symbols.get_symbol_addr p_name) (Z.of_int 3)
      | TTableAddr addr -> Z.logor addr (Z.of_int 3)
      | TRaw v -> v
    in
    let comment = Printf.sprintf "Level %d Entry for VA 0x%s" level (Z.format "%x" va) in
    state.pt_updates <- { addr = entry_addr; data = desc; size = 8; comment } :: state.pt_updates;
    (* Track L3 table address for pte3 calculation *)
    (match va_sym_opt with Some sym -> Hashtbl.replace Symbols.l3_tables sym table_base | None -> ());
    (match alias_opt with Some a -> Hashtbl.add Symbols.symbols a entry_addr | None -> ())
  ) else (
    let key = (Z.to_string table_base) ^ "_" ^ (string_of_int idx) in
    let next = match Hashtbl.find_opt Symbols.symbols key with
      | Some a -> a
      | None ->
          let n = Allocator.alloc (Z.of_int 4096) (Z.of_int 4096) in
          Hashtbl.add Symbols.symbols key n;
          let comment = Printf.sprintf "Level %d Table Pointer for VA 0x%s" level (Z.format "%x" va) in
          state.pt_updates <- { addr = entry_addr; data = Z.logor n (Z.of_int 3); size = 8; comment } :: state.pt_updates;
          n
    in
    install_mapping state next (level + 1) va target force_level alias_opt va_sym_opt
  )

(** Install identity mapping for a physical address *)
let install_identity_mapping state pa =
  let page = Z.logand pa page_mask in
  let desc = Z.logor page (Z.of_int page_descriptor) in
  install_mapping state !(state.root_table) 0 page (TRaw desc) None None None

(** Install identity mappings for an address range *)
let install_identity_range state start_pa end_pa =
  let page_size = Z.of_int 4096 in
  let rec loop curr =
    if Z.gt curr end_pa then ()
    else (
      install_identity_mapping state curr;
      loop (Z.add curr page_size)
    )
  in
  loop (Z.logand start_pa page_mask)

(** =============================================================================
    DSL PROCESSING
    ============================================================================= *)

(** Process page_table_setup DSL statements *)
let rec process_dsl state stmts =
  (* First pass: allocate symbols and check for identity code *)
  List.iter (fun stmt -> match stmt with
    | Decl("virtual", ns) -> List.iter (fun n -> ignore(Symbols.get_virt_symbol n)) ns
    | Decl(_, ns) -> List.iter (fun n -> ignore(Symbols.get_symbol_addr n)) ns
    | Assert(c) -> Symbols.record_constraint c
    | Identity(_, is_code) -> if is_code then state.has_code_identity <- true
    | _ -> ()
  ) stmts;

  (* Second pass: install mappings *)
  List.iter (fun stmt -> match stmt with
    | Identity(a, _) ->
        let pa = Z.of_string a in
        let desc = Z.logor pa (Z.of_int page_descriptor) in
        install_mapping state !(state.root_table) 0 pa (TRaw desc) None None None
    | TableDef { name; addr; body } ->
        let t = Z.of_string addr in
        Hashtbl.add Symbols.symbols name t;
        let sub_state = { state with root_table = ref t } in
        process_dsl sub_state body
    | Mapping { va; target; level; variant; alias } ->
        (* Skip ?-> (variant) mappings - the code will do PTE updates at runtime *)
        if variant then ()
        else begin
          let va_val =
            if String.contains va '(' then Evaluator.eval (Evaluator.parse_string va)
            else Symbols.get_virt_symbol va
          in
          (match target with TPA pa -> Symbols.update_va_mapping_pa va pa | _ -> ());
          install_mapping state !(state.root_table) 0 va_val target level alias (Some va)
        end
    | MemInit(pa, v) ->
        let update = { addr = Symbols.get_symbol_addr pa; data = Z.of_string v; size = 8; comment = "Initial Data" } in
        state.pt_updates <- update :: state.pt_updates
    | _ -> ()
  ) stmts

(** =============================================================================
    PARSING FUNCTIONS
    ============================================================================= *)

(** Parse page_table_setup from TOML *)
let parse_pt_setup toml =
  match Otoml.find_opt toml (fun x -> x) ["page_table_setup"] with
  | Some (Otoml.TomlString s) ->
      let lexbuf = Lexing.from_string s in
      begin try Parser.main_dsl Lexer.read lexbuf with Parser.Error ->
        let pos = Lexing.lexeme_start_p lexbuf in
        failwith (Printf.sprintf "Syntax error at line %d, char %d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol))
      end
  | _ -> []

(** Parse thread definitions from TOML *)
let parse_threads toml arch identity_code_addrs =
  let threads = ref [] in
  let identity_idx = ref 0 in
  (match Otoml.find_opt toml (fun x -> x) ["thread"] with
   | Some (Otoml.TomlTable thread_list) ->
       List.iter (fun (tid, val_toml) ->
         let code_pa =
           if !identity_idx < List.length identity_code_addrs then (
             let a = List.nth identity_code_addrs !identity_idx in
             incr identity_idx; a
           ) else Symbols.get_symbol_addr ("code_" ^ tid)
         in
         match val_toml with
         | Otoml.TomlTable k ->
             (match List.assoc_opt "code" k with
              | Some (Otoml.TomlString asm) ->
                  let instructions = Assembler.encode_assembly ~arch asm in
                  let code_size = Z.of_int (List.length instructions * 4) in
                  let reset_regs = match List.assoc_opt "reset" k with
                    | Some (Otoml.TomlTable regs) -> regs
                    | _ -> []
                  in
                  threads := { tid; code_pa; code_size; instructions; reset_regs } :: !threads
              | _ -> ())
         | _ -> ()
       ) thread_list
   | _ -> ());
  List.sort (fun a b -> String.compare a.tid b.tid) !threads

(** Parse section definitions from TOML *)
let parse_sections toml arch =
  let sections = ref [] in
  (match Otoml.find_opt toml (fun x -> x) ["section"] with
   | Some (Otoml.TomlTable section_list) ->
       List.iter (fun (name, val_toml) ->
         match val_toml with
         | Otoml.TomlTable k ->
             (match List.assoc_opt "address" k, List.assoc_opt "code" k with
              | Some (Otoml.TomlString addr_s), Some (Otoml.TomlString asm) ->
                  let addr = Z.of_string addr_s in
                  let instructions = Assembler.encode_assembly ~arch asm in
                  let size = Z.of_int (List.length instructions * 4) in
                  sections := { sec_name = name; sec_addr = addr; sec_size = size; sec_instructions = instructions } :: !sections
              | _ -> ())
         | _ -> ()
       ) section_list
   | _ -> ());
  !sections

(** =============================================================================
    OUTPUT EMISSION
    ============================================================================= *)

(** Deduplicate memory updates by address (keep last value) *)
let dedup_updates (updates: mem_update list) : mem_update list =
  let tbl = Hashtbl.create 16 in
  List.iter (fun u -> Hashtbl.replace tbl (Z.to_string u.addr) u) updates;
  Hashtbl.fold (fun _ u acc -> u :: acc) tbl []

(** Sort memory updates by address *)
let sort_updates (updates: mem_update list) : mem_update list =
  List.sort (fun a b -> Z.compare a.addr b.addr) updates

(** Emit memory block to output *)
let emit_memory out (u: mem_update) =
  Printf.fprintf out "[[memory]] # %s\nbase = 0x%s\nsize = %d\ndata = 0x%s\n\n"
    u.comment (Z.format "%x" u.addr) u.size (Z.format "%x" u.data)

(** Emit code block to output *)
let emit_code out label pa size instructions =
  let data_str = "[" ^ (String.concat ", " (List.map (Printf.sprintf "0x%x") instructions)) ^ "]" in
  Printf.fprintf out "[[memory]] # %s (PA=0x%s)\nbase = 0x%s\nsize = %d\ndata = %s\n\n"
    label (Z.format "%x" pa) (Z.format "%x" pa) (Z.to_int size) data_str

(** Emit register block to output *)
let emit_registers out thread va root_table =
  let parsed_reg_names = ref [] in
  let parsed_regs = List.map (fun (r, v) ->
    parsed_reg_names := r :: !parsed_reg_names;
    let vs = match v with
      | Otoml.TomlString s -> "0x" ^ (Z.format "%x" (Evaluator.eval (Evaluator.parse_string s)))
      | Otoml.TomlInteger i -> string_of_int i
      | _ -> "0x0"
    in
    Printf.sprintf "%s = %s" r vs
  ) thread.reset_regs in

  let sys_regs = [
    ("SCTLR_EL1", "0x1");
    ("TCR_EL1", "0x0");
    ("ID_AA64MMFR1_EL1", "0x0");
    ("TTBR0_EL1", Printf.sprintf "0x%s" (Z.format "%x" root_table));
    ("ESR_EL1", "0x0"); ("ELR_EL1", "0x0"); ("SPSR_EL1", "0x0"); ("FAR_EL1", "0x0")
  ] |> List.filter (fun (n, _) -> not (List.mem n !parsed_reg_names))
    |> List.map (fun (n, v) -> Printf.sprintf "%s = %s" n v) in

  let has_pstate = List.exists (fun n ->
    n = "PSTATE" || (String.length n > 7 && String.sub n 0 7 = "PSTATE.")
  ) !parsed_reg_names in
  let pstate = if has_pstate then [] else ["PSTATE = { \"EL\" = 0b00, \"SP\" = 0b0 }"] in

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
    thread.tid (Z.format "%x" va)
    (String.concat "\n" (parsed_regs @ sys_regs @ pstate @ default_regs))

(** Emit termination condition *)
let emit_term_cond out tid va size =
  Printf.fprintf out "[[termCond]] # %s\n_PC = 0x%s\n\n" tid (Z.format "%x" (Z.add va size))

(** Emit outcome assertions **)
let emit_outcomes out toml =
  match Otoml.find_opt toml (fun x -> x) ["final"] with
  | Some (Otoml.TomlTable t) ->
    let expect = match List.assoc_opt "expect" t with Some (Otoml.TomlString s) -> s | _ -> "sat" in
    let prefix = if expect = "sat" then "allowed" else "forbidden" in
    (match List.assoc_opt "assertion" t with
      | Some (Otoml.TomlString s) ->
        let s_clean = Str.global_replace (Str.regexp " ") "" s in
        (* Handle trivial assertions - "true" or empty *)
        if s_clean = "true" || s_clean = "" then
          Printf.fprintf out "# No outcome assertion (trivial test)\n\n"
        else (
          let alternatives = if String.contains s_clean '|' then Str.split (Str.regexp "|") s_clean else [s_clean] in
          List.iter (fun alt ->
            let asserts = String.split_on_char '&' alt in
            Printf.fprintf out "[[outcome]]\n";
            let grouped = Hashtbl.create 5 in
            let mem_asserts = ref [] in
            List.iter (fun assertion ->
              match String.split_on_char '=' assertion with
              | [lhs; rhs] ->
                  (* Check if this is a memory assertion: *x=value *)
                  if String.length lhs > 0 && lhs.[0] = '*' then (
                    let symbol = String.sub lhs 1 (String.length lhs - 1) in
                    mem_asserts := (symbol, rhs) :: !mem_asserts
                  ) else (
                    (* Register assertion (tid:reg=value) *)
                    match String.split_on_char ':' lhs with
                    | [tid_s; reg_s] ->
                        let reg_s = Str.global_replace (Str.regexp "^X") "R" (String.trim reg_s) in
                        let existing = try Hashtbl.find grouped tid_s with Not_found -> [] in
                        Hashtbl.replace grouped tid_s ((reg_s, rhs) :: existing)
                    | _ -> ()
                  )
              | _ -> ()
            ) asserts;
            (* Build reg assertions string *)
            let reg_parts = ref [] in
            Hashtbl.iter (fun tid regs ->
              let content = String.concat ", " (List.map (fun (r, v) -> Printf.sprintf "%s = %s" r v) (List.rev regs)) in
              reg_parts := Printf.sprintf "\"%s\" = { %s }" tid content :: !reg_parts
            ) grouped;
            let reg_str = if !reg_parts = [] then "" else String.concat ", " (List.rev !reg_parts) in
            (* Build mem assertions string *)
            let mem_parts = List.filter_map (fun (symbol, value) ->
              (* Try to resolve symbol: first check if it's a direct PA symbol,
                 then check if it's a VA symbol with a PA mapping *)
              let addr_opt =
                match Hashtbl.find_opt Symbols.symbols symbol with
                | Some addr -> Some addr  (* Direct symbol *)
                | None ->
                    (* Check if symbol is in VA mappings *)
                    List.find_map (fun (name, _va, pa_name_opt) ->
                      if name = symbol then
                        match pa_name_opt with
                        | Some pa_name -> Hashtbl.find_opt Symbols.symbols pa_name
                        | None -> None
                      else None
                    ) !Symbols.va_mappings
              in
              match addr_opt with
              | Some addr ->
                  (* Convert value to little-endian 8-byte format *)
                  let int_val = int_of_string value in
                  let le_val = Z.shift_left (Z.of_int int_val) 56 in  (* Shift to MSB position for LE read *)
                  Some (Printf.sprintf "{ addr = 0x%s, value = 0x%s, size = 8 }"
                    (Z.format "%x" addr) (Z.format "%x" le_val))
              | None ->
                  Printf.fprintf out "# Warning: symbol '%s' not resolved, skipping memory assertion\n" symbol;
                  None
            ) !mem_asserts in
            let mem_str = if mem_parts = [] then "" else "[" ^ String.concat ", " mem_parts ^ "]" in
            (* Emit combined format *)
            (match (reg_str, mem_str) with
            | ("", "") -> Printf.fprintf out "%s = {}\n" prefix
            | (r, "") -> Printf.fprintf out "%s = { regs = { %s } }\n" prefix r
            | ("", m) -> Printf.fprintf out "%s = { mem = %s }\n" prefix m
            | (r, m) -> Printf.fprintf out "%s = { regs = { %s }, mem = %s }\n" prefix r m);
            Printf.fprintf out "\n"
          ) alternatives
        )
      | _ -> Printf.fprintf out "# No outcome assertion\n\n")
  | _ -> Printf.fprintf out "# No outcome assertion\n\n"

(** =============================================================================
    MAIN ENTRY POINT
    ============================================================================= *)

let process_toml filename out_channel =
  let toml = Otoml.Parser.from_file filename in
  let arch = match Otoml.find_opt toml (fun x -> x) ["arch"] with
    | Some (Otoml.TomlString s) -> s
    | _ -> "AArch64"
  in
  let name = match Otoml.find_opt toml (fun x -> x) ["name"] with
    | Some (Otoml.TomlString s) -> s
    | _ -> "converted"
  in

  (* Parse page_table_setup DSL *)
  let pt_stmts = parse_pt_setup toml in
  let identity_code_addrs = List.filter_map (function
    | Identity(a, true) -> Some (Z.of_string a)
    | _ -> None
  ) pt_stmts in

  (* Parse threads and sections *)
  let threads = parse_threads toml arch identity_code_addrs in
  let sections = parse_sections toml arch in

  (* Initialize state *)
  let state = {
    pt_updates = [];
    has_code_identity = identity_code_addrs <> [];
    root_table = ref Z.zero;
  } in

  (* Process symbolic variables if no page_table_setup *)
  if pt_stmts = [] then (
    try match Otoml.find toml (fun x -> x) ["symbolic"] with
      | Otoml.TomlArray l ->
          List.iter (function
            | Otoml.TomlString s -> ignore (Symbols.get_symbol_addr s)
            | _ -> ()
          ) l
      | _ -> ()
    with _ -> ()
  );

  (* Compute thread VAs (identity or allocated) *)
  let thread_vas = List.map (fun t ->
    (t.tid, if state.has_code_identity then t.code_pa else Symbols.get_virt_symbol ("code_" ^ t.tid))
  ) threads in

  (* Build page tables if DSL provided *)
  if pt_stmts <> [] then (
    state.root_table := Allocator.alloc (Z.of_int 4096) (Z.of_int 4096);
    Printf.eprintf "Root: 0x%s\n" (Z.format "%x" !(state.root_table));

    process_dsl state pt_stmts;

    (* Zero-init PA symbols that are mapping targets but not explicitly initialized *)
    List.iter (fun (_, _, pa_opt) ->
      match pa_opt with
      | Some pa_name ->
          let pa_addr = Symbols.get_symbol_addr pa_name in
          (* Check if this PA was already initialized via MemInit *)
          let already_init = List.exists (fun u ->
            u.comment = "Initial Data" && Z.equal u.addr pa_addr
          ) state.pt_updates in
          if not already_init then begin
            let update = { addr = pa_addr; data = Z.zero; size = 8; comment = "Initial Data" } in
            state.pt_updates <- update :: state.pt_updates
          end
      | None -> ()
    ) !Symbols.va_mappings;

    (* Identity mappings for allocated PT memory - fixpoint loop because
       installing identity mappings may allocate new tables that also need mappings *)
    let rec install_identity_fixpoint seen_regions =
      let current_regions = !Allocator.used_regions in
      let new_regions = List.filter (fun r -> not (List.mem r seen_regions)) current_regions in
      if new_regions = [] then ()
      else begin
        List.iter (fun (start_addr, end_addr) ->
          install_identity_range state start_addr end_addr
        ) new_regions;
        install_identity_fixpoint current_regions
      end
    in
    install_identity_fixpoint [];

    (* Identity mappings for PA symbols (data addresses) *)
    Hashtbl.iter (fun name addr ->
      if not (String.contains name '_') && not (String.equal name "page_table_base") then
        install_identity_mapping state addr
    ) Symbols.symbols;

    (* Mappings for thread code: VA -> PA (may be identity or different) *)
    List.iter2 (fun t (_, va) ->
      let page_va = Z.logand va page_mask in
      let page_pa = Z.logand t.code_pa page_mask in
      let desc = Z.logor page_pa (Z.of_int page_descriptor) in
      install_mapping state !(state.root_table) 0 page_va (TRaw desc) None None None;
      (* Also install identity mapping for code PA so table walks can access it *)
      if not (Z.equal page_va page_pa) then
        install_identity_mapping state page_pa
    ) threads thread_vas;

    (* Identity mappings for sections *)
    List.iter (fun s ->
      let end_pa = Z.sub (Z.add s.sec_addr s.sec_size) Z.one in
      install_identity_range state s.sec_addr end_pa
    ) sections
  );

  (* === EMIT OUTPUT === *)
  Printf.fprintf out_channel "arch = \"%s\"\nname = \"%s\"\n" arch name;

  (* Symbolic variable mapping comments *)
  if !Symbols.va_mappings <> [] then (
    Printf.fprintf out_channel "# Symbolic Variable Mapping:\n";
    List.iter (fun (n, addr, pa_opt) ->
      let pa_str = match pa_opt with
        | Some p -> (match Hashtbl.find_opt Symbols.symbols p with
            | Some a -> Printf.sprintf " (mapped to PA %s=0x%s)" p (Z.format "%x" a)
            | None -> "")
        | None -> ""
      in
      Printf.fprintf out_channel "# %s = 0x%s%s\n" n (Z.format "%x" addr) pa_str
    ) (List.rev !Symbols.va_mappings);
    Printf.fprintf out_channel "\n"
  );

  (* Emit memory: initial data, page table updates, code, sections *)
  let initial_data, pt_entries = List.partition (fun u -> u.comment = "Initial Data") state.pt_updates in
  let _, pt_entries = List.partition (fun (u: mem_update) -> u.size = 4096) pt_entries in (* Skip 4KB clears *)

  List.iter (emit_memory out_channel) (sort_updates (dedup_updates initial_data));
  List.iter (emit_memory out_channel) (sort_updates (dedup_updates pt_entries));
  List.iter (fun t -> emit_code out_channel ("Code " ^ t.tid) t.code_pa t.code_size t.instructions) threads;
  List.iter (fun s -> emit_code out_channel ("Section " ^ s.sec_name) s.sec_addr s.sec_size s.sec_instructions) sections;

  (* Emit registers *)
  List.iter2 (fun t (_, va) ->
    emit_registers out_channel t va !(state.root_table)
  ) threads thread_vas;

  (* Emit termination conditions *)
  List.iter2 (fun t (_, va) ->
    emit_term_cond out_channel t.tid va t.code_size
  ) threads thread_vas;

  (* Emit outcome assertions *)
  emit_outcomes out_channel toml
