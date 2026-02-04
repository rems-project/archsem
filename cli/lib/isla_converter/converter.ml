(** Main converter for isla-to-archsem conversion.

    Orchestrates the conversion process:
    - Parses isla TOML input
    - Encodes assembly to machine code
    - Allocates code addresses
    - Builds page tables
    - Emits archsem TOML output *)

open Ast
open Types

(** Check if a symbol name is a user-defined PA symbol (not internal) *)
let is_user_pa_symbol name =
  not (String.contains name '_') && not (String.equal name "page_table_base")

(** Check if an address is already initialized in state *)
let is_already_init state addr =
  List.exists (fun (u: Page_tables.mem_update) ->
    u.comment = "Initial Data" && Z.equal u.addr addr
  ) state.Page_tables.pt_updates

(** Find section for a thread by naming convention (threadN_...) *)
let find_section_for_thread tid section_defs =
  let prefix = "thread" ^ tid ^ "_" in
  List.find_opt (fun (s: From_isla.section_def) ->
    String.length s.sec_name >= String.length prefix &&
    String.sub s.sec_name 0 (String.length prefix) = prefix
  ) section_defs

(** Compute thread code PA from thread code pool *)
let compute_thread_code_pa tid =
  let thread_idx = int_of_string tid in
  Z.add Constants.thread_code_base (Z.of_int (thread_idx * Constants.page_size))

(** Encode a thread and its associated section separately *)
let encode_thread_with_section arch section_defs (def: From_isla.thread_def) =
  (* Thread code goes to thread code pool *)
  let thread_instructions = Assembler.encode_assembly ~arch def.code in
  let code_size = Z.of_int (List.length thread_instructions * Constants.instruction_size) in
  let code_pa = compute_thread_code_pa def.tid in

  let thread_info = { tid = def.tid; code_pa; code_size; instructions = thread_instructions; reset_regs = def.reset_regs } in

  (* Check if thread has an associated section *)
  match find_section_for_thread def.tid section_defs with
  | Some sec_def ->
      let sec_instructions = Assembler.encode_assembly ~arch sec_def.sec_code in
      let sec_size = Z.of_int (List.length sec_instructions * Constants.instruction_size) in
      let section_info = { sec_name = sec_def.sec_name; sec_addr = sec_def.sec_addr; sec_size; sec_instructions } in
      (thread_info, Some section_info)
  | None ->
      (thread_info, None)

(** Encode a standalone section (not associated with a thread) *)
let encode_standalone_section arch (def: From_isla.section_def) =
  let sec_instructions = Assembler.encode_assembly ~arch def.sec_code in
  let sec_size = Z.of_int (List.length sec_instructions * Constants.instruction_size) in
  { sec_name = def.sec_name; sec_addr = def.sec_addr; sec_size; sec_instructions }

(** Process symbolic variables for usermode tests *)
let process_usermode_symbols toml state =
  let init_values = Hashtbl.create 16 in
  (try match Otoml.find toml (fun x -> x) ["locations"] with
    | Otoml.TomlTable kvs | Otoml.TomlInlineTable kvs ->
        List.iter (fun (k, v) ->
          let value = match v with
            | Otoml.TomlString s -> Z.of_string s
            | Otoml.TomlInteger i -> Z.of_int i
            | _ -> Z.zero
          in
          Hashtbl.add init_values k value
        ) kvs
    | _ -> ()
  with _ -> ());
  try match Otoml.find toml (fun x -> x) ["symbolic"] with
    | Otoml.TomlArray l ->
        List.iter (function
          | Otoml.TomlString s ->
              let addr = Symbols.get_symbol_addr s in
              let data = match Hashtbl.find_opt init_values s with
                | Some v -> v
                | None -> Z.zero
              in
              let update = { Page_tables.addr; data; size = 8; comment = "Initial Data" } in
              state.Page_tables.pt_updates <- update :: state.Page_tables.pt_updates
          | _ -> ()
        ) l
    | _ -> ()
  with _ -> ()

(** Compute thread virtual addresses *)
let compute_thread_vas ~usermode state threads =
  List.map (fun (t: thread_info) ->
    let pc =
      if usermode then t.code_pa
      else if state.Page_tables.has_code_identity then t.code_pa
      else Symbols.get_virt_symbol ~is_code:true ("code_" ^ t.tid)
    in
    (t.tid, pc)
  ) threads

(** Zero-init PA symbols that are mapping targets but not explicitly initialized *)
let init_unmapped_pa_symbols state =
  (* First, handle VA->PA mappings *)
  List.iter (fun (_, _, pa_opt) ->
    match pa_opt with
    | Some pa_name ->
        let pa_addr = Symbols.get_symbol_addr pa_name in
        if not (is_already_init state pa_addr) then begin
          let update = { Page_tables.addr = pa_addr; data = Z.zero; size = 8; comment = "Initial Data" } in
          state.pt_updates <- update :: state.pt_updates
        end
    | None -> ()
  ) !Symbols.va_mappings;
  (* Also handle all allocated PA symbols (e.g., used directly in desc3) *)
  Hashtbl.iter (fun name addr ->
    if is_user_pa_symbol name && not (is_already_init state addr) then begin
      let update = { Page_tables.addr = addr; data = Z.zero; size = 8; comment = "Initial Data" } in
      state.pt_updates <- update :: state.pt_updates
    end
  ) Symbols.symbols

(** Install identity mappings for all allocated PT memory regions *)
let install_pt_identity_mappings state =
  let rec fixpoint seen_regions =
    let current_regions = !Allocator.used_regions in
    let new_regions = List.filter (fun r -> not (List.mem r seen_regions)) current_regions in
    if new_regions <> [] then begin
      List.iter (fun (start_addr, end_addr) ->
        Page_tables.install_identity_range state start_addr end_addr
      ) new_regions;
      fixpoint current_regions
    end
  in
  fixpoint []

(** Install identity mappings for PA symbols *)
let install_pa_symbol_identity_mappings state =
  let pages_seen = Hashtbl.create 16 in
  Hashtbl.iter (fun name addr ->
    if is_user_pa_symbol name then begin
      let page = Z.logand addr Constants.page_mask in
      if not (Hashtbl.mem pages_seen page) then begin
        Hashtbl.add pages_seen page true;
        Page_tables.install_identity_mapping state page
      end
    end
  ) Symbols.symbols

(** Install mappings for thread code *)
let install_thread_code_mappings state threads thread_vas =
  List.iter2 (fun (t: thread_info) (_, va) ->
    let page_va = Z.logand va Constants.page_mask in
    let page_pa = Z.logand t.code_pa Constants.page_mask in
    let desc = Z.logor page_pa Constants.code_descriptor in
    Page_tables.install_mapping ~is_code:true state !(state.Page_tables.root_table) 0 page_va (TRaw desc) None None None;
    if not (Z.equal page_va page_pa) then
      Page_tables.install_identity_mapping ~is_code:true state page_pa
  ) threads thread_vas

(** Install identity mappings for sections *)
let install_section_mappings state sections =
  List.iter (fun (s: section_info) ->
    let end_pa = Z.sub (Z.add s.sec_addr s.sec_size) Z.one in
    Page_tables.install_identity_range ~is_code:true state s.sec_addr end_pa
  ) sections

(** Build page tables from DSL statements *)
let build_page_tables state pt_stmts threads thread_vas sections =
  state.Page_tables.root_table := Allocator.alloc Constants.page_size_z Constants.page_size_z;

  Page_tables.process_dsl state pt_stmts;
  init_unmapped_pa_symbols state;
  install_pt_identity_mappings state;
  install_pa_symbol_identity_mappings state;
  install_thread_code_mappings state threads thread_vas;
  install_section_mappings state sections

(** Emit symbolic variable mapping comments *)
let emit_va_mapping_comments out_channel =
  if !Symbols.va_mappings <> [] then begin
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
  end

(** Emit memory sections *)
let emit_memory out_channel state =
  let initial_data, pt_entries =
    List.partition (fun (u: Page_tables.mem_update) -> u.comment = "Initial Data") state.Page_tables.pt_updates
  in
  let _, pt_entries =
    List.partition (fun (u: Page_tables.mem_update) -> u.size = Constants.page_size) pt_entries
  in
  List.iter (To_archsem.memory out_channel) (To_archsem.merge_mem_updates (To_archsem.dedup_mem_updates initial_data));
  List.iter (To_archsem.memory out_channel) (To_archsem.merge_mem_updates (To_archsem.dedup_mem_updates pt_entries))

(** Emit code sections for threads and sections *)
let emit_code out_channel threads sections =
  List.iter (fun (t: thread_info) ->
    To_archsem.code out_channel ("Code " ^ t.tid) t.code_pa t.code_size t.instructions
  ) threads;
  List.iter (fun (s: section_info) ->
    To_archsem.code out_channel ("Section " ^ s.sec_name) s.sec_addr s.sec_size s.sec_instructions
  ) sections

(** Emit memory initialization for any symbols discovered after initial memory output *)
let emit_late_symbol_init out_channel state =
  Hashtbl.iter (fun name addr ->
    if is_user_pa_symbol name && not (is_already_init state addr) then begin
      Printf.fprintf out_channel "[[memory]] # Initial Data (late: %s)\n" name;
      Printf.fprintf out_channel "base = 0x%s\nsize = 8\ndata = 0x0\n\n" (Z.format "%x" addr)
    end
  ) Symbols.symbols

(** Emit all output *)
let emit_output out_channel toml arch name ~usermode state threads thread_vas sections =
  Printf.fprintf out_channel "arch = \"%s\"\nname = \"%s\"\n" arch name;
  emit_va_mapping_comments out_channel;
  emit_memory out_channel state;
  emit_code out_channel threads sections;

  let translation_enabled = not usermode in
  List.iter2 (fun t (_, va) ->
    To_archsem.registers out_channel t va !(state.Page_tables.root_table) name ~translation_enabled
  ) threads thread_vas;

  List.iter2 (fun (t: thread_info) (_, va) ->
    To_archsem.term_cond out_channel t.tid va t.code_size sections
  ) threads thread_vas;

  To_archsem.outcomes out_channel toml;

  (* Emit memory for any symbols discovered during register/outcome evaluation *)
  emit_late_symbol_init out_channel state

let process_toml ?(usermode=false) filename out_channel =
  let toml = Otoml.Parser.from_file filename in
  let arch = From_isla.get_arch toml in
  let name = From_isla.get_name toml in

  (* Parse page_table_setup DSL *)
  let pt_stmts = From_isla.parse_pt_setup toml in
  let identity_code_addrs = List.filter_map (function
    | Identity(a, true) -> Some (Z.of_string a)
    | _ -> None
  ) pt_stmts in

  (* Reserve identity-mapped pages before allocating page tables to avoid conflicts *)
  let all_identity_addrs = List.filter_map (function
    | Identity(a, _) -> Some (Z.of_string a)
    | _ -> None
  ) pt_stmts in
  List.iter (fun addr ->
    Allocator.add_region addr Constants.page_size_z
  ) all_identity_addrs;

  (* Parse sections and threads *)
  let section_defs = From_isla.parse_sections toml in
  let thread_defs = From_isla.parse_threads toml in

  (* Reserve thread code pages *)
  List.iter (fun (def: From_isla.thread_def) ->
    let code_pa = compute_thread_code_pa def.tid in
    Allocator.add_region code_pa Constants.page_size_z
  ) thread_defs;

  (* Encode threads and their associated sections separately *)
  let threads_and_sections = List.map
    (encode_thread_with_section arch section_defs)
    thread_defs in
  let threads = List.map fst threads_and_sections in
  let thread_sections = List.filter_map snd threads_and_sections in

  (* Find sections not associated with any thread *)
  let used_section_names = List.map (fun s -> s.sec_name) thread_sections in
  let standalone_section_defs = List.filter
    (fun (s: From_isla.section_def) -> not (List.mem s.sec_name used_section_names))
    section_defs in
  let standalone_sections = List.map (encode_standalone_section arch) standalone_section_defs in
  let sections = thread_sections @ standalone_sections in

  (* Initialize state *)
  let state = {
    Page_tables.pt_updates = [];
    has_code_identity = identity_code_addrs <> [];
    root_table = ref Z.zero;
  } in

  if usermode then process_usermode_symbols toml state;

  let thread_vas = compute_thread_vas ~usermode state threads in

  if pt_stmts <> [] then
    build_page_tables state pt_stmts threads thread_vas sections;

  emit_output out_channel toml arch name ~usermode state threads thread_vas sections
