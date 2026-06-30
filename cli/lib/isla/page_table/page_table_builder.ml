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

type table = Bytes.t

type data_value = Z.t

type layout =
  { root : pa;
    table_entries : (pa * descriptor) list;
    symbols_pa : (string * pa) list;
    phys_symbols_pa : (string * pa) list;
    data_inits : (pa * data_value) list
  }

exception Error of string

let error fmt = Printf.ksprintf (fun msg -> raise (Error msg)) fmt

type t =
  { allocator : Allocator.t;
    root : pa;
    mutable next_table_pa : pa;
    mutable tables : (pa * table) list;
    mutable symbols_pa : (string * pa) list;
    mutable data_inits : (pa * data_value) list
  }

let empty_table () = Bytes.make Desc.table_size '\x00'

let make allocator ~root =
  let tables = [(root, empty_table ())] in
  { allocator;
    tables;
    root;
    next_table_pa = root + Allocator.page_size;
    symbols_pa = [];
    data_inits = []
  }

let check_arch = function
  | Litmus.Arch_id.Arm -> ()
  | arch ->
      error "page_table: only AArch64 is supported, got %s"
        (Litmus.Arch_id.to_string arch)

let alloc_pa builder name =
  match List.assoc_opt name builder.symbols_pa with
  | Some addr -> addr
  | None ->
      let addr = Allocator.alloc_page builder.allocator in
      builder.symbols_pa <- (name, addr) :: builder.symbols_pa;
      addr

(** {1 Table page allocation} *)

(** Allocate a fresh table page and remember its backing bytes. *)
let create_table_page builder =
  if builder.next_table_pa >= builder.root + Allocator.big_size then
    error "page_table: 2MB page-table pool exhausted";
  let addr = builder.next_table_pa in
  builder.next_table_pa <- addr + Allocator.page_size;
  let table = empty_table () in
  builder.tables <- (addr, table) :: builder.tables;
  (addr, table)

let create_child_table builder parent_table idx =
  let (child_addr, child_table) = create_table_page builder in
  Desc.write_entry parent_table idx (Desc.table_descriptor child_addr);
  child_table

(** {1 Mapping path construction} *)

let find_table tables addr =
  match List.assoc_opt addr tables with
  | Some tbl -> tbl
  | None -> error "page_table: table 0x%x not found" addr

let read_child_table_addr table idx =
  Desc.read_entry table idx |> Desc.table_addr_of_descriptor

(** Reuse an existing child table descriptor, or install a new child table. *)
let ensure_child_table builder parent_table idx =
  match read_child_table_addr parent_table idx with
  | Some next_addr -> find_table builder.tables next_addr
  | None -> create_child_table builder parent_table idx

(** {1 Mapping insertion} *)

(** Write a leaf mapping, allowing same writes but rejecting conflicts. *)
let write_leaf table idx va desc =
  let existing = Desc.read_entry table idx in
  if existing <> 0L && existing <> desc then
    error
      "page_table: conflicting mapping for VA 0x%x: existing descriptor 0x%Lx, \
       new descriptor 0x%Lx"
       va existing desc;
  Desc.write_entry table idx desc

(** Align a VA or PA for the descriptor level being inserted. *)
let check_aligned_at_level name level addr =
  let mapping_size = Desc.level_size level in
  if addr mod mapping_size = 0 then addr
  else
    error "page_table: %s 0x%x is not aligned for a level %d mapping" name addr
      level

(** Write an encoded descriptor at [va], allocating intermediate tables. *)
let write_descriptor ?(level = Desc.last_level) builder ~va desc =
  let rec walk table current_level =
    let idx = Desc.va_index va current_level in
    if current_level = level then write_leaf table idx va desc
    else
      let child_table = ensure_child_table builder table idx in
      walk child_table (current_level + 1)
  in
  let root_table = find_table builder.tables builder.root in
  walk root_table Desc.root_level

(** Add the requested mapping, allocating intermediate tables on demand. *)
let add_mapping ?(fields = []) ?(level = Desc.last_level) builder ~va ~pa kind =
  let va = check_aligned_at_level "VA" level va in
  let pa = check_aligned_at_level "PA" level pa in
  let desc =
    try Desc.make_descriptor ~fields ~level ~oa:pa ~kind ()
    with Failure msg -> error "page_table: %s" msg
  in
  write_descriptor ~level builder ~va desc

let add_code_mappings builder code_pages =
  List.iter
    (fun addr -> add_mapping builder ~va:addr ~pa:addr Page_table_ast.Code)
    code_pages

(** {1 Statement evaluation} *)

let eval_mapping_target ?(attrs = []) builder ~va = function
  | Page_table_ast.PaName pa_name ->
      let pa = alloc_pa builder pa_name in
      add_mapping ~fields:attrs builder ~va ~pa Page_table_ast.Data
  | Page_table_ast.Invalid ->
      if attrs <> [] then
        error "page_table: descriptor fields are only supported on PA mappings";
      write_descriptor builder ~va 0L

let eval_stmt builder ~symbolic_vas = function
  | Page_table_ast.Physical names ->
      List.iter (fun name -> ignore (alloc_pa builder name)) names
  | Page_table_ast.Mapping {va_name; target; attrs} ->
      let va =
        match List.assoc_opt va_name symbolic_vas with
        | Some addr -> addr
        | None -> error "page_table: undeclared VA: %s" va_name
      in
      eval_mapping_target ~attrs builder ~va target
  | Page_table_ast.MaybeMapping _ -> ()
  | Page_table_ast.DataInit {pa_name; value} ->
      let pa = alloc_pa builder pa_name in
      builder.data_inits <- (pa, value) :: builder.data_inits
  | Page_table_ast.IdentityMapping {addr; attr} ->
      let addr =
        try Z.to_int addr
        with Z.Overflow ->
          error "page_table: address out of range: %s" (Z.format "%#x" addr)
      in
      add_mapping builder ~va:addr ~pa:addr attr

(** {1 Layout construction} *)

(** Convert mutable table bytes into sparse concrete memory entries. *)
let to_entries builder =
  List.concat_map
    (fun (addr, table) ->
       let n = Bytes.length table / Desc.entry_size in
       List.filter_map
         (fun i ->
            let value = Desc.read_entry table i in
            if value = 0L then None else Some (addr + (i * Desc.entry_size), value)
          )
         (List.init n Fun.id)
     )
    builder.tables

(** Freeze the builder state into the immutable layout used downstream. *)
let to_layout builder =
  let root = builder.root in
  let table_entries = to_entries builder in
  (* Generated PA alias for the root translation-table page. *)
  let symbols_pa = ("page_table_base", root) :: builder.symbols_pa in
  let phys_symbols_pa = List.rev builder.symbols_pa in
  let data_inits = builder.data_inits in
  {root; table_entries; symbols_pa; phys_symbols_pa; data_inits}

let build ~arch ~allocator ~symbolic_vas ~code_pages stmts =
  check_arch arch;
  if stmts = [] then error "page_table: empty page_table_setup";
  (* [root] is the TTBR0 value and the base of the 2MB page-table pool. *)
  let root = Allocator.alloc_big allocator in
  let builder = make allocator ~root in
  (* Page tables are identity-mapped so generated PTE VAs can access them. *)
  add_mapping ~level:2 builder ~va:root ~pa:root Page_table_ast.Data;
  (* Evaluate each statement, using symbolic VAs to resolve virtual names. *)
  List.iter (eval_stmt builder ~symbolic_vas) stmts;
  (* Add code identity mappings after explicit page-table statements. *)
  add_code_mappings builder code_pages;
  (* Put data initializers back in source order. *)
  builder.data_inits <- List.rev builder.data_inits;
  to_layout builder

(** {1 Layout queries} *)

let translate_va_to_pa layout va =
  let desc_at table level =
    let idx = Desc.va_index va level in
    List.assoc_opt (table + (idx * Desc.entry_size)) layout.table_entries
  in
  let rec walk table level =
    match desc_at table level with
    | None -> None
    | Some desc when not (Desc.is_valid desc) -> None
    | Some desc when Desc.is_table level desc ->
        walk (Desc.addr_of_descriptor desc) (level + 1)
    | Some desc ->
        Some
          (Desc.addr_of_descriptor desc + (va land Desc.level_offset_mask level))
  in
  walk layout.root Desc.root_level
