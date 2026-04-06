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

type addr_decl =
  { kind : addr_kind;
    names : string list
  }

type attr_group = (string * Term.t) list

type with_spec_item =
  | WsDefault
  | WsCode
  | WsAttrs of attr_group

type with_spec = with_spec_item list

type stmt =
  | AddrDecl of addr_decl
  | Mapping of
      { va : string;
        pa : string;
        with_spec : with_spec
      }
  | MemInit of
      { addr : string;
        value : Term.t
      }

(** {1 Address allocator} *)

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

type walk_info =
  { walk : string;
    tables : (int * int) list;
    ptes : (int * int) list
  }

type ctx =
  { pa_alloc : alloc;
    va_alloc : alloc;
    auto_imported : string list;
    walks : walk_info list;
    mem_inits : (string * Term.t) list;
    table_data : (int * Bytes.t) list;
    root : int option
  }

let empty_env pa_alloc =
  { pa_alloc;
    va_alloc = alloc_make ~base:(va_base_addr ());
    auto_imported = [];
    walks = [];
    mem_inits = [];
    table_data = [];
    root = None
  }

let resolve_source_addr ctx name =
  match alloc_resolve_opt ctx.va_alloc name with
  | Some addr -> addr
  | None -> (
    match alloc_resolve_opt ctx.pa_alloc name with
    | Some addr -> addr
    | None -> failwith ("pgtable: undeclared address: " ^ name)
  )

let resolve_target_addr ctx name =
  match alloc_resolve_opt ctx.pa_alloc name with
  | Some addr -> addr
  | None -> failwith ("pgtable: undeclared PA: " ^ name)

let declare ctx (decl : addr_decl) =
  List.fold_left
    (fun ctx name ->
       let ctx =
         match decl.kind with
         | Virtual when alloc_resolve_opt ctx.va_alloc name <> None ->
             failwith ("pgtable: duplicate VA name: " ^ name)
         | Physical when alloc_resolve_opt ctx.pa_alloc name <> None ->
             failwith ("pgtable: duplicate PA/IPA name: " ^ name)
         | _ -> ctx
       in
       match decl.kind with
       | Physical ->
           let (pa_alloc, _addr) = alloc_table ctx.pa_alloc name in
           {ctx with pa_alloc}
       | Virtual ->
           let (va_alloc, _addr) = alloc_table ctx.va_alloc name in
           {ctx with va_alloc}
     )
    ctx decl.names

(** Walk page tables from root to [target_level], creating intermediate
    tables as needed. Returns the final table address and data. *)
let walk_or_create ctx va target_level =
  let l0_name = "__pgt_l0" in
  let (ctx, l0_addr) =
    match ctx.root with
    | Some addr -> (ctx, addr)
    | None -> (
      match alloc_resolve_opt ctx.pa_alloc l0_name with
      | Some addr -> (ctx, addr)
      | None ->
          let (pa_alloc, addr) = alloc_table ctx.pa_alloc l0_name in
          ({ctx with pa_alloc}, addr)
    )
  in
  let ctx =
    match ctx.root with Some _ -> ctx | None -> {ctx with root = Some l0_addr}
  in
  let ensure_table_page ctx addr =
    match List.assoc_opt addr ctx.table_data with
    | Some d -> (ctx, d)
    | None ->
        let d = Bytes.make Pgtable_desc.table_size '\x00' in
        ({ctx with table_data = (addr, d) :: ctx.table_data}, d)
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
        let next_addr = existing land 0x0000FFFFFFFFF000 in
        let (ctx, next_data) = ensure_table_page ctx next_addr in
        walk ctx next_addr next_data (level + 1)
          ((level, current_addr) :: tables)
          ((level, pte_addr) :: ptes)
      end
      else begin
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
      (Printf.sprintf "pgtable: %s value %d exceeds %d-bit field width" name value
         width
      );
  let mask = (max_value - 1) lsl shift in
  acc land lnot mask lor (value lsl shift)

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

let map_va_pa ctx va_name pa_name ws =
  let va = resolve_source_addr ctx va_name in
  let pa = resolve_target_addr ctx pa_name in
  let (ctx, _l0_addr, _table_addr, table_data, _tables, _ptes) =
    walk_or_create ctx va 3
  in
  let idx = Pgtable_desc.va_index va 3 in
  let env = make_env ctx in
  let attrs = attrs_of_with_spec ~env ws in
  let desc = Pgtable_desc.page_descriptor pa attrs in
  Pgtable_desc.write_entry table_data idx desc;
  ctx

let eval_stmt ctx = function
  | AddrDecl decl -> declare ctx decl
  | Mapping {va; pa; with_spec} -> map_va_pa ctx va pa with_spec
  | MemInit {addr; value} -> {ctx with mem_inits = (addr, value) :: ctx.mem_inits}

let eval_stmts ctx stmts = List.fold_left eval_stmt ctx stmts

(** {1 Queries and utilities} *)

(** Write an identity L3 page descriptor for [va] into existing page tables. *)
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

(** {1 Main entry point} *)

let evaluate ~(arch : Litmus.Arch_id.t) ~symbolic (stmts : stmt list) =
  if stmts = [] then ([], [], [], None, [], [])
  else begin
    ( match arch with
    | Litmus.Arch_id.Arm -> ()
    | _ -> failwith "pgtable: only AArch64 is supported"
    );
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
