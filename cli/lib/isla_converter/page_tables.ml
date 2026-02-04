(** Page table management for isla-to-archsem conversion.

    This module handles AArch64 page table setup for litmus tests:
    - Installing VA-to-PA mappings at various page table levels
    - Identity mappings for physical addresses
    - Processing page table DSL statements

    Uses 4KB granule with 4-level tables (L0-L3). *)

open Ast

(** Memory update to be emitted in the TOML output *)
type mem_update = {
  addr: Z.t;
  data: Z.t;
  size: int;
  comment: string;
}

(** Accumulated state during page table construction *)
type state = {
  mutable pt_updates: mem_update list;
  mutable has_code_identity: bool;
  root_table: Z.t ref;
}

(* Wire up Symbols module to use Allocator *)
let () = Symbols.allocator_add_region := Allocator.add_region

(** Install a page table mapping from VA to target descriptor *)
let rec install_mapping ?(is_code=false) state table_base level va target force_level alias_opt va_sym_opt =
  let descriptor = if is_code then Constants.code_descriptor else Constants.data_descriptor in
  let shift = Constants.shift_for_level level in
  let idx = Z.to_int (Z.logand (Z.shift_right va shift) Constants.pte_index_mask) in
  let entry_addr = Z.add table_base (Z.of_int (idx * Constants.pte_size)) in
  let is_leaf = level = 3 || (match force_level with Some l -> l = level | None -> false) in

  (* Track L2 table address for pte2 calculation *)
  if level = 2 then
    (match va_sym_opt with Some sym -> Hashtbl.replace Symbols.l2_tables sym table_base | None -> ());

  if is_leaf then (
    let desc = match target with
      | TInvalid -> Z.zero
      | TPA p -> Z.logor (Symbols.get_symbol_addr p) descriptor
      | TTable p_name -> Z.logor (Symbols.get_symbol_addr p_name) Constants.table_descriptor_bits
      | TTableAddr addr -> Z.logor addr Constants.table_descriptor_bits
      | TRaw v -> v
    in
    let comment = Printf.sprintf "Level %d Entry for VA 0x%s" level (Z.format "%x" va) in
    state.pt_updates <- { addr = entry_addr; data = desc; size = Constants.pte_size; comment } :: state.pt_updates;
    (* Track L3 table address for pte3 calculation *)
    (match va_sym_opt with Some sym -> Hashtbl.replace Symbols.l3_tables sym table_base | None -> ());
    (match alias_opt with Some a -> Hashtbl.add Symbols.symbols a entry_addr | None -> ())
  ) else (
    let key = (Z.to_string table_base) ^ "_" ^ (string_of_int idx) in
    let next = match Hashtbl.find_opt Symbols.symbols key with
      | Some a -> a
      | None ->
          let n = Allocator.alloc Constants.page_size_z Constants.page_size_z in
          Hashtbl.add Symbols.symbols key n;
          let comment = Printf.sprintf "Level %d Table Pointer for VA 0x%s" level (Z.format "%x" va) in
          let table_desc = Z.logor n Constants.table_descriptor_bits in
          state.pt_updates <- { addr = entry_addr; data = table_desc; size = Constants.pte_size; comment } :: state.pt_updates;
          n
    in
    install_mapping ~is_code state next (level + 1) va target force_level alias_opt va_sym_opt
  )

(** Install identity mapping (VA = PA) for a physical address *)
let install_identity_mapping ?(is_code=false) state pa =
  let page = Z.logand pa Constants.page_mask in
  let descriptor = if is_code then Constants.code_descriptor else Constants.data_descriptor in
  let desc = Z.logor page descriptor in
  install_mapping state !(state.root_table) 0 page (TRaw desc) None None None

(** Install identity mappings for an address range *)
let install_identity_range ?(is_code=false) state start_pa end_pa =
  let rec loop curr =
    if Z.gt curr end_pa then ()
    else (
      install_identity_mapping ~is_code state curr;
      loop (Z.add curr Constants.page_size_z)
    )
  in
  loop (Z.logand start_pa Constants.page_mask)

(** Process page_table_setup DSL statements *)
let rec process_dsl state stmts =
  (* First pass: allocate symbols and check for identity code *)
  List.iter (fun stmt -> match stmt with
    | Decl("virtual", ns) -> List.iter (fun n -> ignore (Symbols.get_virt_symbol n)) ns
    | Decl(_, ns) -> List.iter (fun n -> ignore (Symbols.get_symbol_addr n)) ns
    | Assert c -> Symbols.record_constraint c
    | Identity(_, is_code) -> if is_code then state.has_code_identity <- true
    | _ -> ()
  ) stmts;

  (* Second pass: install mappings *)
  List.iter (fun stmt -> match stmt with
    | Identity(addr_str, is_code) ->
        let pa = Z.of_string addr_str in
        let descriptor = if is_code then Constants.code_descriptor else Constants.data_descriptor in
        let desc = Z.logor pa descriptor in
        install_mapping ~is_code state !(state.root_table) 0 pa (TRaw desc) None None None
    | TableDef { name; addr; body } ->
        let table_addr = Z.of_string addr in
        Hashtbl.add Symbols.symbols name table_addr;
        let sub_state = { state with root_table = ref table_addr } in
        process_dsl sub_state body
    | Mapping { va; target; level; variant; alias } ->
        if not variant then begin
          let va_val =
            if String.contains va '('
            then Evaluator.eval (Evaluator.parse_expr va)
            else Symbols.get_virt_symbol va
          in
          (match target with TPA pa -> Symbols.update_va_mapping_pa va pa | _ -> ());
          install_mapping state !(state.root_table) 0 va_val target level alias (Some va)
        end
    | MemInit(pa, v) ->
        let update = { addr = Symbols.get_symbol_addr pa; data = Z.of_string v; size = Constants.pte_size; comment = "Initial Data" } in
        state.pt_updates <- update :: state.pt_updates
    | _ -> ()
  ) stmts
