(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
(*      Shreeka Lohani, University of Cambridge                               *)
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

(** Build and query concrete AArch64 page-table layouts. *)

module Desc = Page_table_desc

type va = int

type pa = int

type descriptor = int64

type data_value = Z.t

type layout =
  { default_root : pa option;
    data_symbols_pa : (string, pa) Hashtbl.t;
    data_inits : (pa, data_value) Hashtbl.t
  }

exception Error of string

let error fmt = Printf.ksprintf (fun msg -> raise (Error msg)) fmt

type t =
  { state : Eval_state.t;
    (* Allocates physical addresses for data symbols. *)
    symbol_allocator : Allocator.t;
    (* Allocates root and child translation-table pages. *)
    table_allocator : Allocator.t;
    (* Default root translation-table used when statements are not nested in a
       named table block. *)
    default_root : pa option;
    (* Named translation-table roots. *)
    named_roots : (string, pa) Hashtbl.t;
    (* Page-table descriptors, keyed by their physical addresses. *)
    entries : (pa, descriptor) Hashtbl.t;
    (* Required alignment for each physical-address symbol. *)
    pa_alignments : (string, int) Hashtbl.t;
    (* PA names and their allocated physical addresses. *)
    data_symbols_pa : (string, pa) Hashtbl.t;
    (* Initial data values, keyed by their allocated PAs. *)
    data_inits : (pa, data_value) Hashtbl.t
  }

let make ~state ~symbol_allocator ~table_allocator ~pa_alignments ~default_root =
  Option.iter (Eval_state.add_symbol state "page_table_base") default_root;
  { state;
    symbol_allocator;
    table_allocator;
    default_root;
    named_roots = Hashtbl.create 8;
    entries = Hashtbl.create 256;
    pa_alignments;
    data_symbols_pa = Hashtbl.create 32;
    data_inits = Hashtbl.create 32
  }

let check_arch = function
  | Litmus.Arch_id.Arm -> ()
  | arch ->
      error "page_table: only AArch64 is supported, got %s"
        (Litmus.Arch_id.to_string arch)

let alloc_pa ?(alignment = Allocator.page_size) ?mapping_level builder name =
  let alignment =
    max alignment
      (Hashtbl.find_opt builder.pa_alignments name
      |> Option.value ~default:Allocator.page_size
      )
  in
  match Hashtbl.find_opt builder.data_symbols_pa name with
  | Some addr -> (
      if addr mod alignment = 0 then addr
      else
        match mapping_level with
        | Some level ->
            error
              "page_table: PA symbol %s at 0x%x is not aligned for a level %d \
               mapping (requires %d bytes)"
               name addr level alignment
        | None ->
            error "page_table: PA symbol %s at 0x%x is not aligned to %d bytes"
              name addr alignment
    )
  | None ->
      let addr =
        Allocator.alloc_aligned builder.symbol_allocator ~size:alignment
          ~alignment
      in
      Hashtbl.add builder.data_symbols_pa name addr;
      Eval_state.add_symbol builder.state name addr;
      addr

(** {1 Table roots and page allocation} *)

let addr_of_z name addr =
  try Z.to_int addr
  with Z.Overflow ->
    error "page_table: %s out of range: %s" name (Z.format "%#x" addr)

(* Layout:
   - Code: 0-2 MiB
   - Page tables: 2-4 MiB
   - Data: >= 4 MiB *)
let table_storage_base = Allocator.big_size

let table_storage_limit = table_storage_base + Allocator.big_size

let check_table_addr name addr =
  if addr < table_storage_base || addr >= table_storage_limit then
    error "page_table: %s 0x%x is outside table storage [0x%x, 0x%x)" name addr
      table_storage_base table_storage_limit

let table_addr name value =
  let addr = addr_of_z name value in
  if addr mod Allocator.page_size <> 0 then
    error "page_table: %s 0x%x is not page aligned" name addr;
  check_table_addr name addr;
  addr

(** Allocate a fresh child translation-table page. *)
let create_table_page builder =
  let addr =
    try Allocator.alloc_page builder.table_allocator
    with Failure msg -> error "page_table: %s" msg
  in
  addr

let entry_addr table_addr idx = table_addr + (idx * Desc.entry_size)

let read_entry builder table_addr idx =
  Hashtbl.find_opt builder.entries (entry_addr table_addr idx)

exception Conflicting_entry of pa * descriptor * descriptor

let write_entry builder table_addr idx desc =
  let slot_addr = entry_addr table_addr idx in
  ( match Hashtbl.find_opt builder.entries slot_addr with
  | Some existing when existing <> desc ->
      raise (Conflicting_entry (slot_addr, existing, desc))
  | _ -> ()
  );
  Hashtbl.replace builder.entries slot_addr desc

let create_child_table builder parent_addr idx =
  let child_addr = create_table_page builder in
  try
    write_entry builder parent_addr idx (Desc.table_descriptor child_addr);
    child_addr
  with Conflicting_entry (slot_addr, existing, desc) ->
    error
      "page_table: conflicting mapping for table slot 0x%x: existing descriptor \
       0x%Lx, new descriptor 0x%Lx"
       slot_addr existing desc

let child_table_addr builder table_addr idx =
  Option.bind (read_entry builder table_addr idx) Desc.table_addr_of_descriptor

(** {1 Mapping path construction} *)

(** Reuse an existing child table descriptor, or install a new child table. *)
let ensure_child_table builder parent_addr idx =
  match child_table_addr builder parent_addr idx with
  | Some next_addr -> next_addr
  | None -> create_child_table builder parent_addr idx

(** Align a VA or PA for the descriptor level being inserted. *)
let check_aligned_at_level name level addr =
  let mapping_size = Desc.level_size level in
  if addr mod mapping_size = 0 then addr
  else
    error "page_table: %s 0x%x is not aligned for a level %d mapping" name addr
      level

(** Write an encoded descriptor at [va], allocating intermediate tables. *)
let write_descriptor ?(level = Desc.last_level) builder ~root ~va desc =
  let rec walk table_addr current_level =
    let idx = Desc.va_index va current_level in
    if current_level = level then
      try write_entry builder table_addr idx desc
      with Conflicting_entry (_, existing, desc) ->
        error
          "page_table: conflicting mapping for VA 0x%x: existing descriptor \
           0x%Lx, new descriptor 0x%Lx"
           va existing desc
    else
      let child_addr = ensure_child_table builder table_addr idx in
      walk child_addr (current_level + 1)
  in
  walk root Desc.root_level

(** Add the requested mapping, allocating intermediate tables on demand. *)
let add_mapping
      ?(fields = [])
      ?(level = Desc.last_level)
      builder
      ~root
      ~va
      ~pa
      kind
  =
  let va = check_aligned_at_level "VA" level va in
  let pa = check_aligned_at_level "PA" level pa in
  let desc =
    try Desc.make_descriptor ~fields ~level ~oa:pa ~kind ()
    with Failure msg -> error "page_table: %s" msg
  in
  write_descriptor ~level builder ~root ~va desc

let initialise_root builder ~table_block root =
  add_mapping ~level:2 builder ~root ~va:0 ~pa:0 Page_table_ast.Code;
  add_mapping ~level:2 builder ~root ~va:table_block ~pa:table_block
    Page_table_ast.Data

(** {1 Statement evaluation} *)

let check_table_level = function
  | None -> error "page_table: table descriptors require an explicit level"
  | Some level when level < Desc.root_level || level >= Desc.last_level ->
      error "page_table: table descriptors are only valid at levels %d..%d"
        Desc.root_level (Desc.last_level - 1)
  | Some level -> level

let mapping_alignment level =
  try Desc.level_size level
  with Invalid_argument _ -> error "page_table: invalid mapping level: %d" level

(** Gather alignment requirements for PA targets of explicitly levelled
    mappings. In particular, non-leaf mappings can require more than page
    alignment: [_ -> pa at level 2] requires [pa] to be 2 MiB aligned. *)
let pa_alignment_requests stmts =
  let alignments = Hashtbl.create 32 in
  let rec collect stmts =
    List.iter
      (function
        | Page_table_ast.Mapping
            {target = Page_table_ast.PaName name; level = Some level; _} ->
            let alignment = mapping_alignment level in
            let previous =
              Hashtbl.find_opt alignments name
              |> Option.value ~default:Allocator.page_size
            in
            Hashtbl.replace alignments name (max previous alignment)
        | Page_table_ast.TableBlock {body; _} -> collect body
        | _ -> ()
        )
      stmts
  in
  collect stmts; alignments

let default_tables_enabled stmts =
  List.find_map
    (function Page_table_ast.OptionDefaultTables value -> Some value | _ -> None)
    stmts
  |> Option.value ~default:true

let eval_fields builder fields =
  List.map
    (fun Page_table_ast.{name; value} ->
       Page_table_ast.{name; value = Term.eval ~state:builder.state value}
     )
    fields

let eval_mapping_target ?level ?(attrs = []) builder ~root ~va = function
  | Page_table_ast.PaName pa_name ->
      let alignment = Option.map mapping_alignment level in
      let pa = alloc_pa ?alignment ?mapping_level:level builder pa_name in
      let fields = eval_fields builder attrs in
      add_mapping ?level ~fields builder ~root ~va ~pa Page_table_ast.Data
  | Page_table_ast.Address addr ->
      let pa =
        addr_of_z "mapping address" (Term.eval ~state:builder.state addr)
      in
      let fields = eval_fields builder attrs in
      add_mapping ?level ~fields builder ~root ~va ~pa Page_table_ast.Data
  | Page_table_ast.Invalid ->
      let desc = Desc.apply_descriptor_fields 0L attrs in
      write_descriptor ?level builder ~root ~va desc
  | Page_table_ast.Table addr ->
      if attrs <> [] then
        error "page_table: descriptor fields are only supported on PA mappings";
      let level = check_table_level level in
      let table_pa =
        table_addr "table address" (Term.eval ~state:builder.state addr)
      in
      let desc =
        try Desc.table_descriptor table_pa
        with Failure msg -> error "page_table: %s" msg
      in
      write_descriptor ~level builder ~root ~va desc

let require_root = function
  | Some root -> root
  | None ->
      error
        "page_table: top-level mapping requires an implicit default table, but \
         default_tables = false"

let rec eval_stmt builder ~table_block ~root = function
  | Page_table_ast.OptionDefaultTables _ -> ()
  | Page_table_ast.Virtual _ -> ()
  | Page_table_ast.Physical names ->
      List.iter (fun name -> ignore (alloc_pa builder name)) names
  | Page_table_ast.AlignedVirtual _ -> ()
  | Page_table_ast.Mapping {va_name; target; attrs; level} ->
      let root = require_root root in
      let va =
        match Eval_state.virtual_addr builder.state va_name with
        | Some addr -> addr
        | None -> error "page_table: undeclared VA: %s" va_name
      in
      eval_mapping_target ?level ~attrs builder ~root ~va target
  | Page_table_ast.MaybeMapping _ -> ()
  | Page_table_ast.DataInit {pa_name; value} ->
      let pa = alloc_pa builder pa_name in
      let value = Term.eval ~state:builder.state value in
      Hashtbl.replace builder.data_inits pa value
  | Page_table_ast.IdentityMapping {addr; attr = Page_table_ast.Code} ->
      let addr = addr_of_z "address" (Term.eval ~state:builder.state addr) in
      if addr < Allocator.page_size || addr >= Allocator.big_size then
        error "page_table: identity code address 0x%x is outside the code arena"
          addr
  | Page_table_ast.IdentityMapping {addr; attr = Page_table_ast.Data} ->
      let root = require_root root in
      let addr = addr_of_z "address" (Term.eval ~state:builder.state addr) in
      add_mapping builder ~root ~va:addr ~pa:addr Page_table_ast.Data
  | Page_table_ast.TableBlock {name; base; body; _} ->
      let base = table_addr "table base" base in
      if Hashtbl.mem builder.named_roots name then
        error "page_table: duplicate table root: %s" name;
      if
        builder.default_root = Some base
        || Hashtbl.fold
             (fun _ root duplicate -> duplicate || root = base)
             builder.named_roots false
      then error "page_table: duplicate table base: 0x%x" base;
      Eval_state.add_symbol builder.state name base;
      Hashtbl.add builder.named_roots name base;
      initialise_root builder ~table_block base;
      List.iter (eval_stmt builder ~table_block ~root:(Some base)) body

(** {1 Layout construction} *)

(** Gather root and PA data information for memory generation. *)
let to_layout builder : layout =
  { default_root = builder.default_root;
    data_symbols_pa = builder.data_symbols_pa;
    data_inits = builder.data_inits
  }

let build ~arch ~symbol_allocator ~table_allocator ~table_block ~state stmts =
  check_arch arch;
  if stmts = [] then error "page_table: empty page_table_setup";
  let default_root =
    if default_tables_enabled stmts then
      Some
        ( try Allocator.alloc_page table_allocator
          with Failure msg -> error "page_table: %s" msg
        )
    else None
  in
  let builder =
    make ~state ~symbol_allocator ~table_allocator
      ~pa_alignments:(pa_alignment_requests stmts)
      ~default_root
  in
  state.Eval_state.page_table <- Some builder.entries;
  Option.iter (initialise_root builder ~table_block) builder.default_root;
  ( try List.iter (eval_stmt builder ~table_block ~root:builder.default_root) stmts
    with Failure msg -> error "%s" msg
  );
  to_layout builder
