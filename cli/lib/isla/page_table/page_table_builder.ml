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
    symbols_pa : (string * pa) list;
    phys_symbols_pa : (string * pa) list;
    data_inits : (pa * data_value) list
  }

exception Error of string

let error fmt = Printf.ksprintf (fun msg -> raise (Error msg)) fmt

type t =
  { (* Allocates physical addresses for data symbols. *)
    symbol_allocator : Allocator.t;
    (* Allocates root and child translation-table pages. *)
    table_allocator : Allocator.t;
    (* Root translation-table address. *)
    root : pa;
    (* Page-table descriptors, keyed by their physical addresses. *)
    entries : (pa, descriptor) Hashtbl.t;
    (* Required alignment for each physical-address symbol. *)
    pa_alignments : (string * int) list;
    (* PA names and their allocated physical addresses. *)
    mutable symbols_pa : (string * pa) list;
    (* Initial data values, keyed by their allocated PAs. *)
    mutable data_inits : (pa * data_value) list
  }

let make ~symbol_allocator ~table_allocator ~pa_alignments ~root =
  let entries = Hashtbl.create 256 in
  { symbol_allocator;
    table_allocator;
    entries;
    root;
    pa_alignments;
    symbols_pa = [];
    data_inits = []
  }

let check_arch = function
  | Litmus.Arch_id.Arm -> ()
  | arch ->
      error "page_table: only AArch64 is supported, got %s"
        (Litmus.Arch_id.to_string arch)

let alloc_pa ?(alignment = Allocator.page_size) ?mapping_level builder name =
  let alignment =
    max alignment
      (List.assoc_opt name builder.pa_alignments
      |> Option.value ~default:Allocator.page_size
      )
  in
  match List.assoc_opt name builder.symbols_pa with
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
      builder.symbols_pa <- (name, addr) :: builder.symbols_pa;
      addr

(** {1 Table page allocation} *)

(** Allocate a fresh table page. *)
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
let write_descriptor ?(level = Desc.last_level) builder ~va desc =
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
  walk builder.root Desc.root_level

(** Add the requested mapping, allocating intermediate tables on demand. *)
let add_mapping ?(fields = []) ?(level = Desc.last_level) builder ~va ~pa kind =
  let va = check_aligned_at_level "VA" level va in
  let pa = check_aligned_at_level "PA" level pa in
  let desc =
    try Desc.make_descriptor ~fields ~level ~oa:pa ~kind ()
    with Failure msg -> error "page_table: %s" msg
  in
  write_descriptor ~level builder ~va desc

(** {1 Statement evaluation} *)

let check_table_level = function
  | None -> error "page_table: table descriptors require an explicit level"
  | Some level when level < Desc.root_level || level >= Desc.last_level ->
      error "page_table: table descriptors are only valid at levels %d..%d"
        Desc.root_level (Desc.last_level - 1)
  | Some level -> level

let addr_of_z name addr =
  try Z.to_int addr
  with Z.Overflow ->
    error "page_table: %s out of range: %s" name (Z.format "%#x" addr)

let mapping_alignment level =
  try Desc.level_size level
  with Invalid_argument _ -> error "page_table: invalid mapping level: %d" level

let pa_alignment_requests stmts =
  let requests =
    List.filter_map
      (function
        | Page_table_ast.Mapping
            {target = Page_table_ast.PaName name; level = Some level; _} ->
            Some (name, mapping_alignment level)
        | _ -> None
        )
      stmts
  in
  List.fold_left
    (fun alignments (name, alignment) ->
       let previous =
         List.assoc_opt name alignments
         |> Option.value ~default:Allocator.page_size
       in
       (name, max previous alignment) :: List.remove_assoc name alignments
     )
    [] requests

let eval_mapping_target ?level ?(attrs = []) builder ~va = function
  | Page_table_ast.PaName pa_name ->
      let alignment = Option.map mapping_alignment level in
      let pa = alloc_pa ?alignment ?mapping_level:level builder pa_name in
      add_mapping ?level ~fields:attrs builder ~va ~pa Page_table_ast.Data
  | Page_table_ast.Invalid ->
      if attrs <> [] then
        error "page_table: descriptor fields are only supported on PA mappings";
      write_descriptor ?level builder ~va 0L
  | Page_table_ast.Table addr ->
      if attrs <> [] then
        error "page_table: descriptor fields are only supported on PA mappings";
      let level = check_table_level level in
      let table_pa = addr_of_z "table address" addr in
      let desc =
        try Desc.table_descriptor table_pa
        with Failure msg -> error "page_table: %s" msg
      in
      write_descriptor ~level builder ~va desc

let eval_stmt builder ~symbolic_vas = function
  | Page_table_ast.Virtual _ -> ()
  | Page_table_ast.Physical _ -> ()
  | Page_table_ast.AlignedVirtual _ -> ()
  | Page_table_ast.Mapping {va_name; target; attrs; level} ->
      let va =
        match List.assoc_opt va_name symbolic_vas with
        | Some addr -> addr
        | None -> error "page_table: undeclared VA: %s" va_name
      in
      eval_mapping_target ?level ~attrs builder ~va target
  | Page_table_ast.MaybeMapping _ -> ()
  | Page_table_ast.DataInit {pa_name; value} ->
      let pa = alloc_pa builder pa_name in
      builder.data_inits <- (pa, value) :: builder.data_inits
  | Page_table_ast.IdentityMapping {addr; attr = Page_table_ast.Code} ->
      let addr = addr_of_z "address" addr in
      if addr < Allocator.page_size || addr >= Allocator.big_size then
        error "page_table: identity code address 0x%x is outside the code arena"
          addr
  | Page_table_ast.IdentityMapping {addr; attr = Page_table_ast.Data} ->
      let addr = addr_of_z "address" addr in
      add_mapping builder ~va:addr ~pa:addr Page_table_ast.Data

(** {1 Layout construction} *)

(** Convert table bytes into concrete memory entries. *)
let to_entries builder =
  Hashtbl.fold
    (fun addr desc entries -> (addr, desc) :: entries)
    builder.entries []
  |> List.sort (fun (addr1, _) (addr2, _) -> Int.compare addr1 addr2)

(** Freeze the builder state into the immutable layout used downstream. *)
let to_layout builder =
  let root = builder.root in
  let table_entries = to_entries builder in
  (* Generated PA alias for the root translation-table page. *)
  let symbols_pa = ("page_table_base", root) :: builder.symbols_pa in
  let phys_symbols_pa = List.rev builder.symbols_pa in
  let data_inits = builder.data_inits in
  {root; table_entries; symbols_pa; phys_symbols_pa; data_inits}

let build
      ~arch
      ~symbol_allocator
      ~table_allocator
      ~table_block
      ~symbolic_vas
      stmts
  =
  check_arch arch;
  if stmts = [] then error "page_table: empty page_table_setup";
  let root =
    try Allocator.alloc_page table_allocator
    with Failure msg -> error "page_table: %s" msg
  in
  let builder =
    make ~symbol_allocator ~table_allocator
      ~pa_alignments:(pa_alignment_requests stmts)
      ~root
  in
  add_mapping ~level:2 builder ~va:0 ~pa:0 Page_table_ast.Code;
  add_mapping ~level:2 builder ~va:table_block ~pa:table_block Page_table_ast.Data;
  (* Evaluate each statement, using symbolic VAs to resolve virtual names. *)
  List.iter (eval_stmt builder ~symbolic_vas) stmts;
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
