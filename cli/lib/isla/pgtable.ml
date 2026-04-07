(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
(*      Zongyuan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
(*                                                                            *)
(*  Redistribution and use in source and binary forms, with or without        *)
(*  modification, are permitted provided that the following conditions        *)
(*  are met:                                                                  *)
(*                                                                            *)
(*   1. Redistributions of source code must retain the above copyright        *)
(*      notice, this list of conditions and the following disclaimer.         *)
(*                                                                            *)
(*   2. Redistributions in binary form must reproduce the above copyright     *)
(*      notice, this list of conditions and the following disclaimer in the   *)
(*      documentation and/or other materials provided with the distribution.  *)
(*                                                                            *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS       *)
(*  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT         *)
(*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS         *)
(*  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE            *)
(*  COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,      *)
(*  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,      *)
(*  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS     *)
(*  OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND    *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR     *)
(*  TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE    *)
(*  USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.  *)
(*                                                                            *)
(******************************************************************************)

(** Page table setup DSL: types and evaluator.

    Processes page table DSL statements and produces AArch64 4-level page table
    memory blocks ({!Litmus.Testrepr.memory_block} with [kind = PageTable]).

    Symbolic names from {!Ir.symbolic} are auto-imported as implicit VA
    addresses so that the DSL can use them directly in mappings without
    explicit [virtual] declarations. *)

(** {1 Abstract syntax} *)

type addr_kind =
  | Physical
  | Virtual
  | Intermediate

type addr_decl =
  { kind : addr_kind;
    names : string list;
    alignment : int option
  }

type attr_group = (string * Term.t) list

type with_spec_item =
  | WsDefault
  | WsCode
  | WsAttrs of attr_group

type with_spec = with_spec_item list

type mapping_mod =
  { with_spec : with_spec;
    level : int option;
    walk_name : string option
  }

let no_mod = {with_spec = [WsDefault]; level = None; walk_name = None}

type mapping_source =
  | SrcName of string
  | SrcExpr of Term.t  (** function call, e.g. [pa_to_ipa(table3(walkx))] *)

type mapping_target =
  | PA of string  (** named physical address *)
  | Invalid  (** invalid descriptor — triggers translation fault *)

type identity_target =
  | IdName of string  (** declared address name *)
  | IdAddr of int  (** literal address, e.g. [identity 0x1000] *)
  | IdFn of string * Term.t list
  (** function call, e.g. [identity pa_to_ipa(0x1000)] *)

type table_stage =
  | S1
  | S2

type cmp_op =
  | CmpEq
  | CmpNeq

type assert_expr =
  | AVar of string
  | ASlice of string * int * int  (** name[hi..lo] *)
  | AFn of string * assert_expr list

type stmt =
  | AddrDecl of addr_decl
  | Mapping of
      { va : mapping_source;
        pa : mapping_target;
        modifiers : mapping_mod
      }
  | OptMapping of
      { va : mapping_source;
        pa : mapping_target;
        modifiers : mapping_mod
      }
  | Identity of
      { target : identity_target;
        with_spec : with_spec
      }
  | MemInit of
      { addr : string;
        value : Term.t
      }
  | TableBlock of
      { stage : table_stage;
        name : string;
        base : int;
        body : stmt list
      }
  | TableRef of
      { stage : table_stage;
        name : string
      }
  | Option of
      { name : string;
        value : bool
      }
  | Assert of
      { lhs : assert_expr;
        op : cmp_op;
        rhs : assert_expr
      }

(** {1 Address allocator}

    Bump allocator for PA/VA/table addresses.  Tracks reserved ranges so
    that page-table pages do not collide with code or data. *)

type alloc =
  { mutable next_addr : int;
    mutable table : (string * int) list;
    mutable reserved : (int * int) list
  }

let pa_base_addr () =
  Otoml.find (Litmus.Config.get ()) Otoml.get_integer
    ["isla"; "symbols"; "pa_base_address"]

let va_base_addr () =
  Otoml.find (Litmus.Config.get ()) Otoml.get_integer
    ["isla"; "symbols"; "va_base_address"]

let page_bits () =
  let bits =
    Otoml.find (Litmus.Config.get ()) Otoml.get_integer ["isla"; "page_bits"]
  in
  if bits < 0 then failwith "config: [isla] page_bits must be non-negative";
  bits

let page_size () = 1 lsl page_bits ()

let alloc_make ~base = {next_addr = base; table = []; reserved = []}

let alloc_empty () = alloc_make ~base:(pa_base_addr ())

let alloc_resolve_opt t name = List.assoc_opt name t.table

let alloc_resolve t name =
  match List.assoc_opt name t.table with
  | Some addr -> addr
  | None -> failwith ("pgtable: unknown symbol: " ^ name)

let alloc_register t name addr =
  ( match List.assoc_opt name t.table with
  | Some _ -> ()
  | None -> t.table <- (name, addr) :: t.table
  );
  t

let overlaps addr size (r_addr, r_size) =
  addr < r_addr + r_size && r_addr < addr + size

let alloc_reserve t addr size =
  t.reserved <- (addr, size) :: t.reserved;
  t

let alloc_page t =
  let ps = page_size () in
  let rec find_free addr =
    if List.exists (overlaps addr ps) t.reserved then find_free (addr + ps)
    else addr
  in
  let addr = find_free t.next_addr in
  t.next_addr <- addr + ps;
  addr

let align_up addr alignment =
  let mask = alignment - 1 in
  (addr + mask) land lnot mask

let alloc_table t name =
  match List.assoc_opt name t.table with
  | Some addr -> (t, addr)
  | None ->
      let ts = 4096 in
      let rec find_free addr =
        let addr = align_up addr ts in
        if List.exists (overlaps addr ts) t.reserved then find_free (addr + ts)
        else addr
      in
      let addr = find_free t.next_addr in
      t.next_addr <- addr + ts;
      t.table <- (name, addr) :: t.table;
      t.reserved <- (addr, ts) :: t.reserved;
      (t, addr)

let alloc_data t name =
  match List.assoc_opt name t.table with
  | Some addr -> (t, addr)
  | None ->
      let addr = alloc_page t in
      t.table <- (name, addr) :: t.table;
      (t, addr)

(** {1 Evaluator} *)

open Litmus

(** {2 Walk information} *)

type walk_info =
  { walk : string;
    tables : (int * int) list;  (** (level, table_base_addr) visited *)
    ptes : (int * int) list  (** (level, pte_addr) written *)
  }

(** {2 Internal state} *)

type ctx =
  { pa_alloc : alloc;  (** PA/IPA allocator + name registry *)
    va_alloc : alloc;  (** VA allocator + name registry *)
    auto_imported : string list;
    walks : walk_info list;
    mem_inits : (string * Term.t) list;
    table_data : (int * Bytes.t) list;
    root : int option;  (** Current table root; [None] = auto-allocate __pgt_l0 *)
    named_tables : (string * int) list  (** table name -> base addr *)
  }

(** AArch64 stage 1 page/block descriptor lower attribute fields.
    Each field is (shift, width). Values given in the DSL are interpreted
    as the field value and placed into the field's bit range. *)
let attr_field = function
  | "AttrIndx" -> (2, 3)
  | "NS" -> (5, 1)
  | "AP" -> (6, 2)
  | "SH" -> (8, 2)
  | "AF" -> (10, 1)
  | "nG" -> (11, 1)
  | name -> failwith ("pgtable: unknown attribute field: " ^ name)

let apply_attr ~env acc (name, term) =
  let (shift, width) = attr_field name in
  let value = Z.to_int (Term.eval ~env term) in
  let max_value = 1 lsl width in
  if value < 0 || value >= max_value then
    failwith
      (Printf.sprintf "pgtable: %s value %d exceeds %d-bit field width" name
         value width
      );
  let mask = (max_value - 1) lsl shift in
  (acc land lnot mask) lor (value lsl shift)

(** Compose descriptor attribute bits from a [with_spec].
    [default]/[code] contribute base bitmasks; [\[field = value\]]
    overrides apply on top, clearing the field's bit range before setting.
    This makes "[AP = v] and default" and "default and [AP = v]" equivalent. *)
let attrs_of_with_spec ~env items =
  let base =
    List.fold_left
      (fun acc -> function
         | WsDefault -> acc lor Pgtable_desc.aarch64_data_attrs
         | WsCode -> acc lor Pgtable_desc.aarch64_code_attrs
         | WsAttrs _ -> acc
       )
      0 items
  in
  List.fold_left
    (fun acc -> function
       | WsDefault | WsCode -> acc
       | WsAttrs group -> List.fold_left (apply_attr ~env) acc group
     )
    base items

let ensure_table_page ctx addr =
  match List.assoc_opt addr ctx.table_data with
  | Some d -> (ctx, d)
  | None ->
      let d = Bytes.make Pgtable_desc.table_size '\x00' in
      ({ctx with table_data = (addr, d) :: ctx.table_data}, d)

(** {2 Address resolution} *)

let empty_env pa_alloc =
  { pa_alloc;
    va_alloc = alloc_make ~base:(va_base_addr ());
    auto_imported = [];
    walks = [];
    mem_inits = [];
    table_data = [];
    root = None;
    named_tables = []
  }

(** Resolve mapping source: VA (s1) or IPA (s2). *)
let resolve_source_addr ctx name =
  match alloc_resolve_opt ctx.va_alloc name with
  | Some addr -> addr
  | None -> (
    match alloc_resolve_opt ctx.pa_alloc name with
    | Some addr -> addr
    | None -> failwith ("pgtable: undeclared address: " ^ name)
  )

(** Resolve mapping target: always PA. *)
let resolve_target_addr ctx name =
  match alloc_resolve_opt ctx.pa_alloc name with
  | Some addr -> addr
  | None -> failwith ("pgtable: undeclared PA: " ^ name)

(** {2 Statement processing} *)

let declare ctx (decl : addr_decl) =
  List.fold_left
    (fun ctx name ->
       let ctx =
         match decl.kind with
         | Virtual when alloc_resolve_opt ctx.va_alloc name <> None ->
             if List.mem name ctx.auto_imported then ctx
               (* already auto-imported; skip *)
             else failwith ("pgtable: duplicate VA name: " ^ name)
         | (Physical | Intermediate)
           when alloc_resolve_opt ctx.pa_alloc name <> None ->
             failwith ("pgtable: duplicate PA/IPA name: " ^ name)
         | _ -> ctx
       in
       match decl.kind with
       | Physical | Intermediate ->
           let (pa_alloc, addr) = alloc_table ctx.pa_alloc name in
           ( match decl.alignment with
           | Some align when addr mod align <> 0 ->
               failwith
                 (Printf.sprintf "pgtable: address %s (0x%x) not aligned to %d"
                    name addr align
                 )
           | _ -> ()
           );
           {ctx with pa_alloc}
       | Virtual ->
           let (va_alloc, addr) = alloc_table ctx.va_alloc name in
           ( match decl.alignment with
           | Some align when addr mod align <> 0 ->
               failwith
                 (Printf.sprintf "pgtable: address %s (0x%x) not aligned to %d"
                    name addr align
                 )
           | _ -> ()
           );
           {ctx with va_alloc}
     )
    ctx decl.names

let walk_or_create ctx va target_level =
  let (ctx, l0_addr) =
    match ctx.root with
    | Some addr -> (ctx, addr)
    | None -> (
        let l0_name = "__pgt_l0" in
        match alloc_resolve_opt ctx.pa_alloc l0_name with
        | Some addr -> (ctx, addr)
        | None ->
            let (pa_alloc, addr) = alloc_table ctx.pa_alloc l0_name in
            ({ctx with pa_alloc}, addr)
      )
  in
  let (ctx, l0_data) = ensure_table_page ctx l0_addr in
  let rec walk ctx current_addr current_data level tables ptes =
    if level >= target_level then
      (ctx, current_addr, current_data, List.rev tables, List.rev ptes)
    else
      let idx = Pgtable_desc.va_index va level in
      let pte_addr = current_addr + (idx * Pgtable_desc.entry_size) in
      let existing = Pgtable_desc.read_entry current_data idx in
      if existing land 0x3 = 0x3 && level < target_level then begin
        (* Table descriptor exists, follow it *)
        let next_addr = existing land 0x0000FFFFFFFFF000 in
        let (ctx, next_data) = ensure_table_page ctx next_addr in
        walk ctx next_addr next_data (level + 1)
          ((level, current_addr) :: tables)
          ((level, pte_addr) :: ptes)
      end
      else begin
        (* Create new intermediate table *)
        let next_name = Printf.sprintf "__pgt_%x_%d_%d" va level idx in
        let (pa_alloc, next_addr) = alloc_table ctx.pa_alloc next_name in
        let ctx = {ctx with pa_alloc} in
        let next_data = Bytes.make Pgtable_desc.table_size '\x00' in
        let ctx =
          {ctx with table_data = (next_addr, next_data) :: ctx.table_data}
        in
        let desc = Pgtable_desc.table_descriptor next_addr in
        Pgtable_desc.write_entry current_data idx desc;
        walk ctx next_addr next_data (level + 1)
          ((level, current_addr) :: tables)
          ((level, pte_addr) :: ptes)
      end
  in
  let (ctx, final_addr, final_data, tables, ptes) =
    walk ctx l0_addr l0_data 0 [] []
  in
  (ctx, l0_addr, final_addr, final_data, tables, ptes)

let make_env ctx = function
  | Term.Mem sym -> (
    match alloc_resolve_opt ctx.va_alloc sym with
    | Some addr -> Some (Z.of_int addr)
    | None -> (
      match alloc_resolve_opt ctx.pa_alloc sym with
      | Some addr -> Some (Z.of_int addr)
      | None -> None
    )
  )
  | Term.Reg _ -> None

let resolve_source ctx (src : mapping_source) =
  match src with
  | SrcName name -> resolve_source_addr ctx name
  | SrcExpr _ ->
      failwith "pgtable: function-call mapping sources not yet supported"

let map
      ctx
      (va_src : mapping_source)
      (target : mapping_target)
      (mods : mapping_mod)
  =
  let va = resolve_source ctx va_src in
  let target_level = Option.value mods.level ~default:3 in
  if target_level < 1 || target_level > 3 then
    failwith
      (Printf.sprintf "pgtable: target level %d out of valid range [1..3]"
         target_level
      );
  let (ctx, _l0_addr, table_addr, table_data, tables, ptes) =
    walk_or_create ctx va target_level
  in
  let idx = Pgtable_desc.va_index va target_level in
  let pte_addr = table_addr + (idx * Pgtable_desc.entry_size) in
  let env = make_env ctx in
  let desc =
    match target with
    | Invalid ->
        (* Invalid descriptor: all zeros — no valid bit set *)
        0
    | PA pa_name ->
        let pa = resolve_target_addr ctx pa_name in
        if target_level < 3 then begin
          let block_size = 1 lsl Pgtable_desc.level_shift target_level in
          if pa land (block_size - 1) <> 0 then
            failwith
              (Printf.sprintf
                 "pgtable: PA 0x%x not aligned to block size 0x%x for level %d" pa
                 block_size target_level
              )
        end;
        let attrs = attrs_of_with_spec ~env mods.with_spec in
        if target_level = 3 then Pgtable_desc.page_descriptor pa attrs
        else Pgtable_desc.block_descriptor pa target_level attrs
  in
  Pgtable_desc.write_entry table_data idx desc;
  let tables = tables @ [(target_level, table_addr)] in
  let ptes = ptes @ [(target_level, pte_addr)] in
  match mods.walk_name with
  | Some name -> {ctx with walks = {walk = name; tables; ptes} :: ctx.walks}
  | None -> ctx

let identity_map ctx (target : identity_target) with_spec =
  let resolve_any ctx name =
    match alloc_resolve_opt ctx.va_alloc name with
    | Some addr -> addr
    | None -> (
      match alloc_resolve_opt ctx.pa_alloc name with
      | Some addr -> addr
      | None -> failwith ("pgtable: undeclared address: " ^ name)
    )
  in
  let (ctx, name, addr) =
    match target with
    | IdName name -> (ctx, name, resolve_any ctx name)
    | IdAddr addr ->
        let ctx =
          { ctx with
            pa_alloc = alloc_reserve ctx.pa_alloc addr Pgtable_desc.table_size;
            va_alloc = alloc_reserve ctx.va_alloc addr Pgtable_desc.table_size
          }
        in
        (ctx, Printf.sprintf "__identity_%x" addr, addr)
    | IdFn _ -> raise Exit
  in
  let va_key = name ^ "__identity_va" in
  let pa_key = name ^ "__identity_pa" in
  let ctx =
    { ctx with
      va_alloc = alloc_register ctx.va_alloc va_key addr;
      pa_alloc = alloc_register ctx.pa_alloc pa_key addr
    }
  in
  let mods : mapping_mod = {with_spec; level = None; walk_name = None} in
  map ctx (SrcName va_key) (PA pa_key) mods

let stage_str = function S1 -> "s1table" | S2 -> "s2table"

let validate_nesting parent_stage body =
  List.iter
    (function
      | TableBlock {stage; name; _} ->
          if stage = parent_stage then
            failwith
              (Printf.sprintf "pgtable: cannot nest %s %s inside %s"
                 (stage_str stage) name (stage_str parent_stage)
              );
          if parent_stage = S1 && stage = S2 then
            failwith
              (Printf.sprintf "pgtable: cannot nest %s %s inside s1table"
                 (stage_str stage) name
              )
      | _ -> ()
      )
    body

let rec init_table ctx (stage : table_stage) name base body =
  validate_nesting stage body;
  if List.mem_assoc name ctx.named_tables then
    failwith ("pgtable: duplicate table name: " ^ name);
  (* Reserve the base address and register the table name *)
  let ctx =
    { ctx with
      pa_alloc = alloc_reserve ctx.pa_alloc base Pgtable_desc.table_size;
      named_tables = (name, base) :: ctx.named_tables
    }
  in
  let ctx = {ctx with pa_alloc = alloc_register ctx.pa_alloc name base} in
  (* Process body with this table as root *)
  let saved_root = ctx.root in
  let ctx = {ctx with root = Some base} in
  let ctx = eval_stmts ctx body in
  {ctx with root = saved_root}

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
       | Mapping {va; pa; modifiers} -> map ctx va pa modifiers
       | OptMapping _ -> ctx (* ignored: axiomatic only *)
       | Identity {target; with_spec} -> (
         try identity_map ctx target with_spec with Exit -> ctx
       )
       | MemInit {addr; value} ->
           {ctx with mem_inits = (addr, value) :: ctx.mem_inits}
       | TableBlock {stage; name; base; body} ->
           init_table ctx stage name base body
       | TableRef {stage; name} -> use_table ctx stage name
       | Option _ -> ctx (* parsed but ignored for now *)
       | Assert _ -> ctx (* address constraints: axiomatic only *)
     )
    ctx stmts

(** {2 Page table queries}

    Used to evaluate [pteN], [descN], and [mkdescN] expressions
    against already-built page table data. *)

(** Write an identity L3 page descriptor for [va] into existing page tables.

    Walks from [base] through L0->L1->L2 (which must already exist as table
    descriptors) and writes a code page descriptor at L3[Pgtable_desc.va_index va 3].
    If the L3 slot is already occupied, does nothing. *)
let add_identity_code_entry ~table_data ~base va =
  let rec find_l3_tbl addr lvl =
    if lvl = 3 then addr
    else
      let tbl = List.assoc addr table_data in
      let idx = Pgtable_desc.va_index va lvl in
      let desc = Pgtable_desc.read_entry tbl idx in
      if desc land 0x3 <> 0x3 then
        failwith
          (Printf.sprintf
             "pgtable: cannot add identity mapping for 0x%x — no table \
              descriptor at level %d"
              va lvl
          );
      let next = desc land 0x0000FFFFFFFFF000 in
      find_l3_tbl next (lvl + 1)
  in
  let l3_addr = find_l3_tbl base 0 in
  let l3_tbl = List.assoc l3_addr table_data in
  let idx = Pgtable_desc.va_index va 3 in
  let existing = Pgtable_desc.read_entry l3_tbl idx in
  if existing = 0 then
    Pgtable_desc.write_entry l3_tbl idx
      (Pgtable_desc.page_descriptor va Pgtable_desc.aarch64_code_attrs)

(** Convert full page table buffers to sparse memory blocks.

    Instead of emitting whole 4KB pages (which create 4096 gmap entries each,
    mostly zeros), emit only the non-zero 8-byte entries.  This reduces the
    initial memory map size from ~16K entries to ~50, giving orders-of-magnitude
    speedup in the promising model. *)
let to_sparse_blocks (table_data : (int * Bytes.t) list) =
  List.concat_map
    (fun (addr, data) ->
       let n = Bytes.length data / Pgtable_desc.entry_size in
       let blocks = ref [] in
       for i = n - 1 downto 0 do
         let offset = i * Pgtable_desc.entry_size in
         let nonzero = ref false in
         for j = 0 to Pgtable_desc.entry_size - 1 do
           if Bytes.get data (offset + j) <> '\x00' then nonzero := true
         done;
         if !nonzero then
           blocks :=
             { Testrepr.addr = addr + offset;
               step = Pgtable_desc.entry_size;
               data = Bytes.sub data offset Pgtable_desc.entry_size;
               sym = None;
               kind = Testrepr.PageTable
             }
             :: !blocks
       done;
       !blocks
     )
    table_data

(** {2 Main entry point} *)

let evaluate ~(arch : Litmus.Arch_id.t) ~symbolic (stmts : stmt list) =
  if stmts = [] then ([], [], [], None, [], [])
  else begin
    ( match arch with
    | Litmus.Arch_id.Arm -> ()
    | _ -> failwith "pgtable: only AArch64 is supported"
    );
    (* Auto-import symbolic names as implicit VA addresses *)
    let ctx =
      List.fold_left
        (fun ctx sym ->
           match alloc_resolve_opt ctx.pa_alloc sym with
           | Some addr ->
               { ctx with
                 va_alloc = alloc_register ctx.va_alloc sym addr;
                 auto_imported = sym :: ctx.auto_imported
               }
           | None ->
               let (pa_alloc, addr) = alloc_data ctx.pa_alloc sym in
               { ctx with
                 pa_alloc;
                 va_alloc = alloc_register ctx.va_alloc sym addr;
                 auto_imported = sym :: ctx.auto_imported
               }
         )
        (empty_env (alloc_empty ()))
        symbolic
    in
    let ctx = eval_stmts ctx stmts in
    let memory =
      List.map
        (fun (addr, data) ->
           { Testrepr.addr;
             step = Pgtable_desc.entry_size;
             data;
             sym = None;
             kind = Testrepr.PageTable
           }
         )
        ctx.table_data
    in
    let l0_addr = alloc_resolve_opt ctx.pa_alloc "__pgt_l0" in
    ( match l0_addr with
    | Some l0 -> ignore (alloc_register ctx.pa_alloc "page_table_base" l0)
    | None -> ()
    );
    (* Build VA->PA map by walking the page table for each VA *)
    let va_pa_map =
      match l0_addr with
      | Some base ->
          List.filter_map
            (fun (name, va) ->
               try
                 let desc =
                   Pgtable_desc.lookup_desc_value ~table_data:ctx.table_data ~base
                     va 3
                 in
                 if desc land 0x3 = 0x3 then
                   let pa_page = desc land 0x0000FFFFFFFFF000 in
                   let offset = va land 0xFFF in
                   Some (name, pa_page lor offset)
                 else None
               with _ -> None
             )
            ctx.va_alloc.table
      | None -> []
    in
    ( memory,
      List.rev ctx.walks,
      List.rev ctx.mem_inits,
      l0_addr,
      va_pa_map,
      ctx.pa_alloc.table @ ctx.va_alloc.table
    )
  end
