(** Page table setup DSL: types and evaluator.

    Processes page table DSL statements and produces AArch64 4-level page table
    memory blocks ({!Litmus.Testrepr.memory_block} with [kind = PageTable]).

    Symbolic names from {!Ir.symbolic} are auto-imported as implicit VA
    addresses so that the DSL can use them directly in mappings without
    explicit [virtual] declarations. *)

(** {1 Abstract syntax} *)

type addr_kind = Physical | Virtual | Intermediate

type addr_decl = {
  kind : addr_kind;
  names : string list;
  alignment : int option;
}

type attr_group = (string * Term.t) list

type with_spec_item =
  | WsDefault
  | WsCode
  | WsAttrs of attr_group

type with_spec = with_spec_item list

type mapping_mod = {
  with_spec : with_spec;
  level : int option;
  walk_name : string option;
}

let no_mod = { with_spec = [WsDefault]; level = None; walk_name = None }

type mapping_source =
  | SrcName of string
  | SrcExpr of Term.t  (** function call, e.g. [pa_to_ipa(table3(walkx))] *)

type mapping_target =
  | PA of string      (** named physical address *)
  | Invalid           (** invalid descriptor — triggers translation fault *)

type identity_target =
  | IdName of string  (** declared address name *)
  | IdAddr of int     (** literal address, e.g. [identity 0x1000] *)
  | IdFn of string * Term.t list  (** function call, e.g. [identity pa_to_ipa(0x1000)] *)

type table_stage = S1 | S2

type cmp_op = CmpEq | CmpNeq

type assert_expr =
  | AVar of string
  | ASlice of string * int * int   (** name[hi..lo] *)
  | AFn of string * assert_expr list

type stmt =
  | AddrDecl of addr_decl
  | Mapping of { va : mapping_source; pa : mapping_target; modifiers : mapping_mod }
  | OptMapping of { va : mapping_source; pa : mapping_target; modifiers : mapping_mod }
  | Identity of { target : identity_target; with_spec : with_spec }
  | MemInit of { addr : string; value : Term.t }
  | TableBlock of { stage : table_stage; name : string;
                    base : int; body : stmt list }
  | TableRef of { stage : table_stage; name : string }
  | Option of { name : string; value : bool }
  | Assert of { lhs : assert_expr; op : cmp_op; rhs : assert_expr }

(** {1 Evaluator} *)

open Litmus

(** {2 Walk information} *)

type walk_info = {
  walk : string;
  tables : (int * int) list;   (** (level, table_base_addr) visited *)
  ptes : (int * int) list;     (** (level, pte_addr) written *)
}

(** {2 Internal state} *)

type ctx = {
  pa_alloc : Symbols.t;  (** PA/IPA allocator + name registry *)
  va_alloc : Symbols.t;  (** VA allocator + name registry *)
  auto_imported : string list;
  walks : walk_info list;
  mem_inits : (string * Term.t) list;
  table_data : (int * Bytes.t) list;
  root : int option;  (** Current table root; [None] = auto-allocate __pgt_l0 *)
  named_tables : (string * int) list;  (** table name -> base addr *)
}

let table_size = 4096
let entry_size = 8

let level_shift = function
  | 0 -> 39 | 1 -> 30 | 2 -> 21 | 3 -> 12
  | n -> failwith (Printf.sprintf "pgtable: invalid level %d" n)

let va_index va level =
  (va lsr level_shift level) land 0x1FF

(** {2 Descriptor encoding (AArch64)}

    Attribute bits are stored WITHOUT the type field (bits 1:0).
    Each descriptor constructor is solely responsible for setting the type:
    - table descriptor: bits 1:0 = 0b11
    - page descriptor (L3): bits 1:0 = 0b11
    - block descriptor (L1/L2): bits 1:0 = 0b01 *)

let table_descriptor next_table_pa =
  (next_table_pa land 0x0000FFFFFFFFF000) lor 0x3

(* Attribute bits only (no type field).  Matches isla S1PageAttrs::default().
   AF=1 (bit 10) | AP=0b01 (bits 7:6, EL1 R/W) | SH=0b00 | AttrIndx=0b000 *)
let default_data_attrs = 0x440

(* Matches isla S1PageAttrs::code().
   AF=1 (bit 10) | AP=0b11 (bits 7:6, EL1 R/O) | SH=0b00 | AttrIndx=0b000 *)
let default_code_attrs = 0x4C0

let page_descriptor pa attrs =
  (pa land 0x0000FFFFFFFFF000) lor attrs lor 0x3

let block_descriptor pa level attrs =
  let shift = level_shift level in
  let mask = (-1) lsl shift in
  (pa land mask land 0x0000FFFFFFFFFFFF) lor attrs lor 0x1

(** Return attribute bits (2 and above) for the given with_spec. *)
let attrs_of_with_spec ~env items =
  List.fold_left
    (fun acc item ->
      match item with
      | WsDefault -> acc lor default_data_attrs
      | WsCode -> acc lor default_code_attrs
      | WsAttrs group ->
        List.fold_left
          (fun acc (_, v) -> acc lor Z.to_int (Term.eval ~env v))
          acc group)
    0 items

(** {2 Table read/write helpers} *)

let write_entry data idx value =
  let offset = idx * entry_size in
  for i = 0 to 7 do
    let byte = (value lsr (i * 8)) land 0xFF in
    Bytes.set data (offset + i) (Char.chr byte)
  done

let read_entry data idx =
  let offset = idx * entry_size in
  let v = ref 0 in
  for i = 7 downto 0 do
    v := (!v lsl 8) lor Char.code (Bytes.get data (offset + i))
  done;
  !v

let alloc_table ctx addr =
  match List.assoc_opt addr ctx.table_data with
  | Some d -> (ctx, d)
  | None ->
    let d = Bytes.make table_size '\x00' in
    ({ ctx with table_data = (addr, d) :: ctx.table_data }, d)

(** {2 Address resolution} *)

let empty_env pa_alloc = {
  pa_alloc;
  va_alloc = Symbols.make ~base:(Symbols.va_base_addr ());
  auto_imported = [];
  walks = [];
  mem_inits = [];
  table_data = [];
  root = None;
  named_tables = [];
}

(** Resolve mapping source: VA (s1) or IPA (s2). *)
let resolve_source_addr ctx name =
  match Symbols.resolve_opt ctx.va_alloc name with
  | Some addr -> addr
  | None ->
    match Symbols.resolve_opt ctx.pa_alloc name with
    | Some addr -> addr
    | None -> failwith ("pgtable: undeclared address: " ^ name)

(** Resolve mapping target: always PA. *)
let resolve_target_addr ctx name =
  match Symbols.resolve_opt ctx.pa_alloc name with
  | Some addr -> addr
  | None -> failwith ("pgtable: undeclared PA: " ^ name)

(** {2 Statement processing} *)

let declare ctx (decl : addr_decl) =
  List.fold_left
    (fun ctx name ->
      let ctx =
        match decl.kind with
        | Virtual when Symbols.resolve_opt ctx.va_alloc name <> None ->
          if List.mem name ctx.auto_imported then
            ctx  (* already auto-imported; skip *)
          else
            failwith ("pgtable: duplicate VA name: " ^ name)
        | Physical | Intermediate when Symbols.resolve_opt ctx.pa_alloc name <> None ->
          failwith ("pgtable: duplicate PA/IPA name: " ^ name)
        | _ -> ctx
      in
      match decl.kind with
      | Physical | Intermediate ->
        let pa_alloc, addr = Symbols.alloc_table ctx.pa_alloc name in
        (match decl.alignment with
         | Some align when addr mod align <> 0 ->
           failwith (Printf.sprintf
             "pgtable: address %s (0x%x) not aligned to %d" name addr align)
         | _ -> ());
        { ctx with pa_alloc }
      | Virtual ->
        let va_alloc, addr = Symbols.alloc_table ctx.va_alloc name in
        (match decl.alignment with
         | Some align when addr mod align <> 0 ->
           failwith (Printf.sprintf
             "pgtable: address %s (0x%x) not aligned to %d" name addr align)
         | _ -> ());
        { ctx with va_alloc })
    ctx decl.names

let walk_or_create ctx va target_level =
  let ctx, l0_addr = match ctx.root with
    | Some addr -> (ctx, addr)
    | None ->
      let l0_name = "__pgt_l0" in
      (match Symbols.resolve_opt ctx.pa_alloc l0_name with
       | Some addr -> (ctx, addr)
       | None ->
         let pa_alloc, addr = Symbols.alloc_table ctx.pa_alloc l0_name in
         ({ ctx with pa_alloc }, addr))
  in
  let ctx, l0_data = alloc_table ctx l0_addr in
  let rec walk ctx current_addr current_data level tables ptes =
    if level >= target_level then
      (ctx, current_addr, current_data, List.rev tables, List.rev ptes)
    else
      let idx = va_index va level in
      let pte_addr = current_addr + idx * entry_size in
      let existing = read_entry current_data idx in
      if existing land 0x3 = 0x3 && level < target_level then begin
        (* Table descriptor exists, follow it *)
        let next_addr = existing land 0x0000FFFFFFFFF000 in
        let ctx, next_data = alloc_table ctx next_addr in
        walk ctx next_addr next_data (level + 1)
          ((level, current_addr) :: tables)
          ((level, pte_addr) :: ptes)
      end else begin
        (* Create new intermediate table *)
        let next_name = Printf.sprintf "__pgt_%x_%d_%d" va level idx in
        let pa_alloc, next_addr = Symbols.alloc_table ctx.pa_alloc next_name in
        let ctx = { ctx with pa_alloc } in
        let next_data = Bytes.make table_size '\x00' in
        let ctx = { ctx with table_data = (next_addr, next_data) :: ctx.table_data } in
        let desc = table_descriptor next_addr in
        write_entry current_data idx desc;
        walk ctx next_addr next_data (level + 1)
          ((level, current_addr) :: tables)
          ((level, pte_addr) :: ptes)
      end
  in
  let ctx, final_addr, final_data, tables, ptes =
    walk ctx l0_addr l0_data 0 [] []
  in
  (ctx, l0_addr, final_addr, final_data, tables, ptes)

let make_env ctx = function
  | Term.Mem sym ->
    (match Symbols.resolve_opt ctx.va_alloc sym with
     | Some addr -> Some (Z.of_int addr)
     | None ->
       match Symbols.resolve_opt ctx.pa_alloc sym with
       | Some addr -> Some (Z.of_int addr)
       | None -> None)
  | Term.Reg _ -> None

let resolve_source ctx (src : mapping_source) =
  match src with
  | SrcName name -> resolve_source_addr ctx name
  | SrcExpr _ ->
    failwith "pgtable: function-call mapping sources not yet supported"

let map ctx (va_src : mapping_source)
    (target : mapping_target) (mods : mapping_mod) =
  let va = resolve_source ctx va_src in
  let target_level = Option.value mods.level ~default:3 in
  if target_level < 1 || target_level > 3 then
    failwith (Printf.sprintf
      "pgtable: target level %d out of valid range [1..3]" target_level);
  let ctx, _l0_addr, table_addr, table_data, tables, ptes =
    walk_or_create ctx va target_level
  in
  let idx = va_index va target_level in
  let pte_addr = table_addr + idx * entry_size in
  let env = make_env ctx in
  let desc = match target with
    | Invalid ->
      (* Invalid descriptor: all zeros — no valid bit set *)
      0
    | PA pa_name ->
      let pa = resolve_target_addr ctx pa_name in
      if target_level < 3 then begin
        let block_size = 1 lsl level_shift target_level in
        if pa land (block_size - 1) <> 0 then
          failwith (Printf.sprintf
            "pgtable: PA 0x%x not aligned to block size 0x%x for level %d"
            pa block_size target_level)
      end;
      let attrs = attrs_of_with_spec ~env mods.with_spec in
      if target_level = 3 then page_descriptor pa attrs
      else block_descriptor pa target_level attrs
  in
  write_entry table_data idx desc;
  let tables = tables @ [(target_level, table_addr)] in
  let ptes = ptes @ [(target_level, pte_addr)] in
  match mods.walk_name with
  | Some name ->
    { ctx with walks = { walk = name; tables; ptes } :: ctx.walks }
  | None -> ctx

let identity_map ctx (target : identity_target) with_spec =
  let resolve_any ctx name =
    match Symbols.resolve_opt ctx.va_alloc name with
    | Some addr -> addr
    | None ->
      match Symbols.resolve_opt ctx.pa_alloc name with
      | Some addr -> addr
      | None -> failwith ("pgtable: undeclared address: " ^ name)
  in
  let ctx, name, addr = match target with
    | IdName name -> (ctx, name, resolve_any ctx name)
    | IdAddr addr ->
      let ctx = { ctx with
        pa_alloc = Symbols.reserve ctx.pa_alloc addr table_size;
        va_alloc = Symbols.reserve ctx.va_alloc addr table_size }
      in
      (ctx, Printf.sprintf "__identity_%x" addr, addr)
    | IdFn _ ->
      raise Exit
  in
  let va_key = name ^ "__identity_va" in
  let pa_key = name ^ "__identity_pa" in
  let ctx = { ctx with
    va_alloc = Symbols.register ctx.va_alloc va_key addr;
    pa_alloc = Symbols.register ctx.pa_alloc pa_key addr }
  in
  let mods : mapping_mod =
    { with_spec; level = None; walk_name = None }
  in
  map ctx (SrcName va_key) (PA pa_key) mods

let rec init_table ctx (stage : table_stage) name base body =
  ignore stage;  (* stage distinction reserved for future S2 support *)
  if List.mem_assoc name ctx.named_tables then
    failwith ("pgtable: duplicate table name: " ^ name);
  (* Reserve the base address and register the table name *)
  let ctx = { ctx with
    pa_alloc = Symbols.reserve ctx.pa_alloc base table_size;
    named_tables = (name, base) :: ctx.named_tables }
  in
  let ctx = { ctx with pa_alloc = Symbols.register ctx.pa_alloc name base } in
  (* Process body with this table as root *)
  let saved_root = ctx.root in
  let ctx = { ctx with root = Some base } in
  let ctx = eval_stmts ctx body in
  { ctx with root = saved_root }

and use_table ctx (_stage : table_stage) name =
  (* Table reference: just ensure the name is registered.
     In isla, this maps the referenced table into the parent scope.
     For now, the table must already be defined. *)
  match List.assoc_opt name ctx.named_tables with
  | Some _addr -> ctx
  | None -> failwith ("pgtable: undefined table: " ^ name)

and eval_stmts ctx stmts =
  List.fold_left
    (fun ctx stmt ->
      match stmt with
      | AddrDecl decl -> declare ctx decl
      | Mapping { va; pa; modifiers } ->
        map ctx va pa modifiers
      | OptMapping _ -> ctx  (* ignored: axiomatic only *)
      | Identity { target; with_spec } ->
        (try identity_map ctx target with_spec with Exit -> ctx)
      | MemInit { addr; value } ->
        { ctx with mem_inits = (addr, value) :: ctx.mem_inits }
      | TableBlock { stage; name; base; body } ->
        init_table ctx stage name base body
      | TableRef { stage; name } ->
        use_table ctx stage name
      | Option _ -> ctx  (* parsed but ignored for now *)
      | Assert _ -> ctx  (* address constraints: axiomatic only *))
    ctx stmts

(** {2 Page table queries}

    Used to evaluate [pteN], [descN], and [mkdescN] expressions
    against already-built page table data. *)

let lookup_pte_addr ~table_data ~base va level =
  let rec walk addr lvl =
    if lvl = level then
      addr + va_index va level * entry_size
    else
      let tbl = List.assoc addr table_data in
      let idx = va_index va lvl in
      let desc = read_entry tbl idx in
      if desc land 0x3 <> 0x3 then
        failwith (Printf.sprintf
          "pgtable: no table descriptor at level %d for VA 0x%x" lvl va);
      let next = desc land 0x0000FFFFFFFFF000 in
      walk next (lvl + 1)
  in
  walk base 0

let lookup_desc_value ~table_data ~base va level =
  let rec walk addr lvl =
    let tbl = List.assoc addr table_data in
    let idx = va_index va lvl in
    if lvl = level then
      read_entry tbl idx
    else
      let desc = read_entry tbl idx in
      if desc land 0x3 <> 0x3 then
        failwith (Printf.sprintf
          "pgtable: no table descriptor at level %d for VA 0x%x" lvl va);
      let next = desc land 0x0000FFFFFFFFF000 in
      walk next (lvl + 1)
  in
  walk base 0

let make_desc ~level ~oa ~attrs () =
  if level = 3 then page_descriptor oa attrs
  else block_descriptor oa level attrs

(** Write an identity L3 page descriptor for [va] into existing page tables.

    Walks from [base] through L0->L1->L2 (which must already exist as table
    descriptors) and writes a code page descriptor at L3[va_index va 3].
    If the L3 slot is already occupied, does nothing. *)
let add_identity_code_entry ~table_data ~base va =
  let rec find_l3_tbl addr lvl =
    if lvl = 3 then addr
    else
      let tbl = List.assoc addr table_data in
      let idx = va_index va lvl in
      let desc = read_entry tbl idx in
      if desc land 0x3 <> 0x3 then
        failwith (Printf.sprintf
          "pgtable: cannot add identity mapping for 0x%x — \
           no table descriptor at level %d" va lvl);
      let next = desc land 0x0000FFFFFFFFF000 in
      find_l3_tbl next (lvl + 1)
  in
  let l3_addr = find_l3_tbl base 0 in
  let l3_tbl = List.assoc l3_addr table_data in
  let idx = va_index va 3 in
  let existing = read_entry l3_tbl idx in
  if existing = 0 then
    write_entry l3_tbl idx (page_descriptor va default_code_attrs)

(** Convert full page table buffers to sparse memory blocks.

    Instead of emitting whole 4KB pages (which create 4096 gmap entries each,
    mostly zeros), emit only the non-zero 8-byte entries.  This reduces the
    initial memory map size from ~16K entries to ~50, giving orders-of-magnitude
    speedup in the promising model. *)
let to_sparse_blocks (table_data : (int * Bytes.t) list) =
  List.concat_map (fun (addr, data) ->
    let n = Bytes.length data / entry_size in
    let blocks = ref [] in
    for i = n - 1 downto 0 do
      let offset = i * entry_size in
      let nonzero = ref false in
      for j = 0 to entry_size - 1 do
        if Bytes.get data (offset + j) <> '\x00' then nonzero := true
      done;
      if !nonzero then
        blocks := {
          Testrepr.addr = addr + offset;
          step = entry_size;
          data = Bytes.sub data offset entry_size;
          sym = None;
          kind = Testrepr.PageTable;
        } :: !blocks
    done;
    !blocks)
  table_data

(** {2 Main entry point} *)

let evaluate ~(arch : Litmus.Arch_id.t) ~symbolic syms
    (stmts : stmt list) =
  if stmts = [] then
    (syms, [], [], [], None, [], [])
  else begin
    (match arch with
     | Litmus.Arch_id.Arm -> ());
    (* Auto-import symbolic names as implicit VA addresses *)
    let ctx = List.fold_left
      (fun ctx sym ->
        match Symbols.resolve_opt ctx.pa_alloc sym with
        | Some addr ->
          { ctx with va_alloc = Symbols.register ctx.va_alloc sym addr;
                     auto_imported = sym :: ctx.auto_imported }
        | None ->
          let pa_alloc, addr = Symbols.alloc_data ctx.pa_alloc sym in
          { ctx with
            pa_alloc;
            va_alloc = Symbols.register ctx.va_alloc sym addr;
            auto_imported = sym :: ctx.auto_imported })
      (empty_env syms) symbolic
    in
    let ctx = eval_stmts ctx stmts
    in
    let memory =
      List.map
        (fun (addr, data) ->
          { Testrepr.addr; step = entry_size; data;
            sym = None; kind = Testrepr.PageTable })
        ctx.table_data
    in
    let l0_addr = Symbols.resolve_opt ctx.pa_alloc "__pgt_l0" in
    let pa_alloc = match l0_addr with
      | Some l0 -> Symbols.register ctx.pa_alloc "page_table_base" l0
      | None -> ctx.pa_alloc
    in
    (* Build VA->PA map by walking the page table for each VA *)
    let va_pa_map = match l0_addr with
      | Some base ->
        List.filter_map (fun (name, va) ->
          try
            let desc = lookup_desc_value ~table_data:ctx.table_data
              ~base va 3 in
            if desc land 0x3 = 0x3 then
              let pa_page = desc land 0x0000FFFFFFFFF000 in
              let offset = va land 0xFFF in
              Some (name, pa_page lor offset)
            else None
          with _ -> None)
          ctx.va_alloc.table
      | None -> []
    in
    (pa_alloc, memory, List.rev ctx.walks, List.rev ctx.mem_inits, l0_addr,
     va_pa_map, ctx.va_alloc.table)
  end
