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
  { root : pa;
    table_entries : (pa * descriptor) list;
    table_symbols_pa : (string * pa) list;
    data_symbols_pa : (string * pa) list;
    data_inits : (pa * data_value) list
  }

exception Error of string

let error fmt = Printf.ksprintf (fun msg -> raise (Error msg)) fmt

type table_root =
  { stage : Page_table_ast.table_stage;
    name : string option;
    base : pa;
    mutable next_table_pa : pa
  }

type t =
  { allocator : Allocator.t;
    default_root : table_root;
    mutable roots : table_root list;
    mutable table_pages : pa list;
    entries : (pa, descriptor) Hashtbl.t;
    mutable declared_pa_names_rev : string list;
    mutable data_symbols_pa : (string * pa) list;
    mutable data_inits : (pa * data_value) list
  }

let make allocator ~root =
  let default_root =
    { stage = Page_table_ast.S1;
      name = None;
      base = root;
      next_table_pa = root + Allocator.page_size
    }
  in
  { allocator;
    default_root;
    roots = [default_root];
    table_pages = [root];
    entries = Hashtbl.create 256;
    declared_pa_names_rev = [];
    data_symbols_pa = [];
    data_inits = []
  }

let check_arch = function
  | Litmus.Arch_id.Arm -> ()
  | arch ->
      error "page_table: only AArch64 is supported, got %s"
        (Litmus.Arch_id.to_string arch)

let alloc_physical ?(alignment = Allocator.page_size) ?mapping_level builder name =
  match List.assoc_opt name builder.data_symbols_pa with
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
        Allocator.alloc_aligned builder.allocator ~size:Allocator.page_size
          ~alignment
      in
      builder.data_symbols_pa <- (name, addr) :: builder.data_symbols_pa;
      addr

(** {1 Table page allocation} *)

let addr_of_z name addr =
  try Z.to_int addr
  with Z.Overflow ->
    error "page_table: %s out of range: %s" name (Z.format "%#x" addr)

let find_root builder ~stage ~name =
  match
    List.find_opt
      (fun root -> root.stage = stage && root.name = Some name)
      builder.roots
  with
  | Some root -> root
  | None -> error "page_table: unknown table root: %s" name

let reserve_root builder ~stage ~name ~base =
  let base = addr_of_z "table base" base in
  if base mod Allocator.page_size <> 0 then
    error "page_table: table base 0x%x is not page aligned" base;
  if
    List.exists
      (fun root -> root.stage = stage && root.name = Some name)
      builder.roots
  then error "page_table: duplicate table root: %s" name;
  if List.exists (fun root -> root.base = base) builder.roots then
    error "page_table: duplicate table base: 0x%x" base;
  let root =
    {stage; name = Some name; base; next_table_pa = base + Allocator.page_size}
  in
  builder.roots <- root :: builder.roots;
  builder.table_pages <- base :: builder.table_pages

let rec reserve_table_roots builder = function
  | [] -> ()
  | Page_table_ast.TableBlock {stage; name; base; body} :: stmts ->
      reserve_root builder ~stage ~name ~base;
      reserve_table_roots builder body;
      reserve_table_roots builder stmts
  | _ :: stmts -> reserve_table_roots builder stmts

(** Allocate a fresh table page in [root]'s 2MB table pool. *)
let create_table_page builder root =
  let rec find_free addr =
    if addr >= root.base + Allocator.big_size then
      error "page_table: 2MB page-table pool exhausted";
    if List.mem addr builder.table_pages then
      find_free (addr + Allocator.page_size)
    else addr
  in
  let addr = find_free root.next_table_pa in
  root.next_table_pa <- addr + Allocator.page_size;
  builder.table_pages <- addr :: builder.table_pages;
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

let create_child_table builder root parent_addr idx =
  let child_addr = create_table_page builder root in
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
let ensure_child_table builder root parent_addr idx =
  match child_table_addr builder parent_addr idx with
  | Some next_addr -> next_addr
  | None -> create_child_table builder root parent_addr idx

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
      let child_addr = ensure_child_table builder root table_addr idx in
      walk child_addr (current_level + 1)
  in
  walk root.base Desc.root_level

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

let add_code_mappings builder ~root code_pages =
  List.iter
    (fun addr -> add_mapping builder ~root ~va:addr ~pa:addr Page_table_ast.Code)
    code_pages

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

let eval_mapping_target ?level ?(attrs = []) builder ~root ~va = function
  | Page_table_ast.PaName pa_name ->
      let alignment = Option.map mapping_alignment level in
      let pa = alloc_physical ?alignment ?mapping_level:level builder pa_name in
      add_mapping ?level ~fields:attrs builder ~root ~va ~pa Page_table_ast.Data
  | Page_table_ast.Invalid ->
      if attrs <> [] then
        error "page_table: descriptor fields are only supported on PA mappings";
      write_descriptor ?level builder ~root ~va 0L
  | Page_table_ast.Table addr ->
      if attrs <> [] then
        error "page_table: descriptor fields are only supported on PA mappings";
      let level = check_table_level level in
      let table_pa = addr_of_z "table address" addr in
      let desc =
        try Desc.table_descriptor table_pa
        with Failure msg -> error "page_table: %s" msg
      in
      write_descriptor ~level builder ~root ~va desc

let rec eval_stmt builder ~symbolic_vas ~root = function
  | Page_table_ast.Virtual _ -> ()
  | Page_table_ast.Physical names ->
      builder.declared_pa_names_rev <-
        List.rev_append names builder.declared_pa_names_rev
  | Page_table_ast.AlignedVirtual _ -> ()
  | Page_table_ast.Mapping {va_name; target; attrs; level} ->
      let va =
        match List.assoc_opt va_name symbolic_vas with
        | Some addr -> addr
        | None -> error "page_table: undeclared VA: %s" va_name
      in
      eval_mapping_target ?level ~attrs builder ~root ~va target
  | Page_table_ast.MaybeMapping _ -> ()
  | Page_table_ast.DataInit {pa_name; value} ->
      let pa = alloc_physical builder pa_name in
      builder.data_inits <- (pa, value) :: builder.data_inits
  | Page_table_ast.IdentityMapping {addr; attr} ->
      let addr = addr_of_z "address" addr in
      add_mapping builder ~root ~va:addr ~pa:addr attr
  | Page_table_ast.TableBlock {stage; name; base = _; body} ->
      let root = find_root builder ~stage ~name in
      List.iter (eval_stmt builder ~symbolic_vas ~root) body

(** {1 Layout construction} *)

(** Convert table bytes into concrete memory entries. *)
let to_entries builder =
  Hashtbl.fold
    (fun addr desc entries -> (addr, desc) :: entries)
    builder.entries []
  |> List.sort (fun (addr1, _) (addr2, _) -> Int.compare addr1 addr2)

(** Freeze the builder state into the immutable layout used downstream. *)
let to_layout builder =
  let root = builder.default_root.base in
  let table_entries = to_entries builder in
  let table_symbols_pa =
    List.filter_map
      (fun root -> Option.map (fun name -> (name, root.base)) root.name)
      builder.roots
    |> List.rev
  in
  let data_symbols_pa = List.rev builder.data_symbols_pa in
  let data_inits = builder.data_inits in
  {root; table_entries; table_symbols_pa; data_symbols_pa; data_inits}

let build ~arch ~allocator ~symbolic_vas ~code_pages stmts =
  check_arch arch;
  if stmts = [] then error "page_table: empty page_table_setup";
  (* [root] is the TTBR0 value and the base of the 2MB page-table pool. *)
  let root = Allocator.alloc_big allocator in
  let builder = make allocator ~root in
  reserve_table_roots builder stmts;
  (* Page tables are identity-mapped so generated PTE VAs can access them. *)
  add_mapping ~level:2 builder ~root:builder.default_root ~va:root ~pa:root
    Page_table_ast.Data;
  (* Evaluate each statement, using symbolic VAs to resolve virtual names. *)
  List.iter (eval_stmt builder ~symbolic_vas ~root:builder.default_root) stmts;
  (* Materialize PA symbols that were declared but never otherwise used. *)
  List.iter
    (fun name -> ignore (alloc_physical builder name))
    (List.rev builder.declared_pa_names_rev);
  (* Add code identity mappings after explicit page-table statements. *)
  add_code_mappings builder ~root:builder.default_root code_pages;
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
