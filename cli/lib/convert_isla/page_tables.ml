open Ast

(** Memory update to be emitted in the TOML output *)
type mem_update = { addr: Z.t; data: Z.t; size: int; comment: string }

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
    Bits [7:6]  = AP[2:1] Access permissions
    Bits [9:8]  = 0b11  SH (Inner Shareable)
    Bit  [10]   = 1     AF (Access Flag) — must be set
    Bit  [11]   = 0     nG (non-Global)
    Bits [47:12] = PA   Output physical address
    Bit  [53]   = PXN   Privileged Execute Never
    Bit  [54]   = UXN   Unprivileged Execute Never

    Code descriptor: 0x6C3 = AP=11 (RO EL1&EL0), AF=1, SH=11, UXN=0, PXN=0 (executable)
    Data descriptor: 0x60000000000743 = AP=01 (RW), UXN=1, PXN=1 (non-executable)
    With PA: (PA & ~0xFFF) | descriptor *)
let code_descriptor = Z.of_int 0x6C3  (* Read-only for EL1 and EL0, executable *)
let data_descriptor = Z.of_string "0x60000000000743"  (* Read-write, non-executable *)
let page_descriptor = 0x743  (* Legacy: kept for compatibility *)
let page_mask = Z.of_string "0xFFFFFFFFFFFFF000"

(* Wire up Symbols module to use Allocator for page registration *)
let () = Symbols.allocator_add_region := Allocator.add_region

(** =============================================================================
    PAGE TABLE INSTALLATION
    ============================================================================= *)

(** Install a page table mapping from VA to target descriptor.
    ~is_code: if true, use executable descriptor; otherwise use data descriptor *)
let rec install_mapping ?(is_code=false) state table_base level va target force_level alias_opt va_sym_opt =
  let get_descriptor () = if is_code then code_descriptor else data_descriptor in
  let shift = match level with 0->39 | 1->30 | 2->21 | 3->12 | _->0 in
  let idx = Z.to_int (Z.logand (Z.shift_right va shift) (Z.of_int 0x1FF)) in
  let entry_addr = Z.add table_base (Z.of_int (idx * 8)) in
  let is_leaf = level = 3 || (match force_level with Some l -> l = level | None -> false) in

  if is_leaf then (
    let desc = match target with
      | TInvalid -> Z.zero
      | TPA p -> Z.logor (Symbols.get_symbol_addr p) (get_descriptor ())
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
    install_mapping ~is_code state next (level + 1) va target force_level alias_opt va_sym_opt
  )

(** Install identity mapping for a physical address.
    ~is_code: if true, map as executable code (default: false = data) *)
let install_identity_mapping ?(is_code=false) state pa =
  let page = Z.logand pa page_mask in
  let descriptor = if is_code then code_descriptor else data_descriptor in
  let desc = Z.logor page descriptor in
  install_mapping state !(state.root_table) 0 page (TRaw desc) None None None

(** Install identity mappings for an address range.
    ~is_code: if true, map as executable code (default: false = data) *)
let install_identity_range ?(is_code=false) state start_pa end_pa =
  let page_size = Z.of_int 4096 in
  let rec loop curr =
    if Z.gt curr end_pa then ()
    else (
      install_identity_mapping ~is_code state curr;
      loop (Z.add curr page_size)
    )
  in
  loop (Z.logand start_pa page_mask)

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

  (* Second pass: install mappings (skip variant mappings - they're for axiomatic models) *)
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
        if variant then
          ()  (* Skip variant mappings (?->) - they're for axiomatic models *)
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
