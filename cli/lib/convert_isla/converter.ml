open Ast

let process_toml ?(usermode=false) filename out_channel =
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
  let pt_stmts = Input_parser.parse_pt_setup toml in
  let identity_code_addrs = List.filter_map (function
    | Identity(a, true) -> Some (Z.of_string a)
    | _ -> None
  ) pt_stmts in

  (* Parse threads and sections *)
  let threads = Input_parser.parse_threads toml arch identity_code_addrs in
  let sections = Input_parser.parse_sections toml arch in

  (* Initialize state *)
  let state = {
    Page_tables.pt_updates = [];
    has_code_identity = identity_code_addrs <> [];
    root_table = ref Z.zero;
  } in

  (* Process symbolic variables for usermode tests *)
  if usermode then (
    try match Otoml.find toml (fun x -> x) ["symbolic"] with
      | Otoml.TomlArray l ->
          List.iter (function
            | Otoml.TomlString s ->
                let addr = Symbols.get_symbol_addr s in
                (* Add zero initialization for usermode data symbols *)
                let update = { Page_tables.addr; data = Z.zero; size = 8; comment = "Initial Data" } in
                state.pt_updates <- update :: state.pt_updates
            | _ -> ()
          ) l
      | _ -> ()
    with _ -> ()
  );

  (* Compute thread PCs (physical for usermode/identity, virtual otherwise) *)
  let thread_vas = List.map (fun (t: Input_parser.thread_info) ->
    let pc =
      if usermode then
        (* Usermode: use physical address directly *)
        t.code_pa
      else if state.has_code_identity then
        (* Identity-mapped: VA = PA *)
        t.code_pa
      else
        (* Virtual: allocate VA *)
        Symbols.get_virt_symbol ~is_code:true ("code_" ^ t.tid)
    in
    (t.tid, pc)
  ) threads in

  (* Build page tables if DSL provided *)
  if pt_stmts <> [] then (
    state.root_table := Allocator.alloc (Z.of_int 4096) (Z.of_int 4096);
    Printf.eprintf "Root: 0x%s\n" (Z.format "%x" !(state.root_table));

    Page_tables.process_dsl state pt_stmts;

    (* Zero-init PA symbols that are mapping targets but not explicitly initialized *)
    List.iter (fun (_, _, pa_opt) ->
      match pa_opt with
      | Some pa_name ->
          let pa_addr = Symbols.get_symbol_addr pa_name in
          (* Check if this PA was already initialized via MemInit *)
          let already_init = List.exists (fun (u: Page_tables.mem_update) ->
            u.comment = "Initial Data" && Z.equal u.addr pa_addr
          ) state.pt_updates in
          if not already_init then begin
            let update = { Page_tables.addr = pa_addr; data = Z.zero; size = 8; comment = "Initial Data" } in
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
          Page_tables.install_identity_range state start_addr end_addr
        ) new_regions;
        install_identity_fixpoint current_regions
      end
    in
    install_identity_fixpoint [];

    (* Identity mappings for PA symbols (data addresses) - one per shared page *)
    let pages_seen = Hashtbl.create 16 in
    Hashtbl.iter (fun name addr ->
      if not (String.contains name '_') && not (String.equal name "page_table_base") then begin
        let page = Z.logand addr Page_tables.page_mask in
        if not (Hashtbl.mem pages_seen page) then begin
          Hashtbl.add pages_seen page true;
          Page_tables.install_identity_mapping state page
        end
      end
    ) Symbols.symbols;

    (* Mappings for thread code: VA -> PA (executable, read-only) *)
    List.iter2 (fun (t: Input_parser.thread_info) (_, va) ->
      let page_va = Z.logand va Page_tables.page_mask in
      let page_pa = Z.logand t.code_pa Page_tables.page_mask in
      let desc = Z.logor page_pa Page_tables.code_descriptor in  (* Use executable descriptor *)
      Page_tables.install_mapping ~is_code:true state !(state.root_table) 0 page_va (TRaw desc) None None None;
      (* Also install identity mapping for code PA so table walks can access it *)
      if not (Z.equal page_va page_pa) then
        Page_tables.install_identity_mapping ~is_code:true state page_pa
    ) threads thread_vas;

    (* Identity mappings for sections (code, e.g. exception handlers) *)
    List.iter (fun (s: Input_parser.section_info) ->
      let end_pa = Z.sub (Z.add s.sec_addr s.sec_size) Z.one in
      Page_tables.install_identity_range ~is_code:true state s.sec_addr end_pa
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
  let initial_data, pt_entries = List.partition (fun (u: Page_tables.mem_update) -> u.comment = "Initial Data") state.pt_updates in
  let _, pt_entries = List.partition (fun (u: Page_tables.mem_update) -> u.size = 4096) pt_entries in (* Skip 4KB clears *)

  List.iter (Output_emitter.emit_memory out_channel) (Output_emitter.merge_adjacent_updates (Output_emitter.dedup_updates initial_data));
  List.iter (Output_emitter.emit_memory out_channel) (Output_emitter.merge_adjacent_updates (Output_emitter.dedup_updates pt_entries));
  List.iter (fun (t: Input_parser.thread_info) -> Output_emitter.emit_code out_channel ("Code " ^ t.tid) t.code_pa t.code_size t.instructions) threads;
  List.iter (fun (s: Input_parser.section_info) -> Output_emitter.emit_code out_channel ("Section " ^ s.sec_name) s.sec_addr s.sec_size s.sec_instructions) sections;

  (* Emit registers *)
  let translation_enabled = not usermode in
  List.iter2 (fun t (_, va) ->
    Output_emitter.emit_registers out_channel t va !(state.root_table) name ~translation_enabled
  ) threads thread_vas;

  (* Emit termination conditions *)
  List.iter2 (fun (t: Input_parser.thread_info) (_, va) ->
    Output_emitter.emit_term_cond out_channel t.tid va t.code_size sections
  ) threads thread_vas;

  (* Emit outcome assertions *)
  Output_emitter.emit_outcomes out_channel toml
