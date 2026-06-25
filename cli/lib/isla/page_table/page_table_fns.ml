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

(** Page-table helper functions available in Isla expressions. *)

(** Return the PA of the PTE selected by [va] at [level], walking table
    entries from the root translation-table PA [base]. *)
let pte_addr name entries ~base ~va ~level =
  let rec walk table current_level =
    let index = Page_table_desc.va_index va current_level in
    let addr = table + (index * Page_table_desc.entry_size) in
    if current_level = level then addr
    else
      let desc = List.assoc_opt addr entries |> Option.value ~default:0L in
      match Page_table_desc.table_addr_of_descriptor desc with
      | Some next_table -> walk next_table (current_level + 1)
      | None ->
          Fn_registry.error "%s: no table descriptor at level %d for VA 0x%x" name
            current_level va
  in
  walk base Page_table_desc.root_level

(** [page(a)] extracts a 4KB page number from an address. *)
let page_function =
  ( "page",
    { Fn_registry.params = ["a"];
      defaults = [];
      eval =
        (function
          | [a] ->
              Z.logand (Z.shift_right a 12) (Z.sub (Z.shift_left Z.one 36) Z.one)
          | args -> Fn_registry.arity_error "page" 1 (List.length args)
          )
    }
  )

(** [asid(v)] shifts an ASID value into bits [63:48]. *)
let asid_function =
  ( "asid",
    { Fn_registry.params = ["v"];
      defaults = [];
      eval =
        (function
          | [v] -> Z.shift_left v 48
          | args -> Fn_registry.arity_error "asid" 1 (List.length args)
          )
    }
  )

(** [pteN(va, base)] treats [base] as the root translation-table PA, then
    returns the VA of the matching PTE in the page-table VA window. *)
let pte_function page_table_va_base entries level =
  let name = Printf.sprintf "pte%d" level in
  ( name,
    { Fn_registry.params = ["va"; "base"];
      defaults = [];
      eval =
        (function
          | [va; base] ->
              let va = Fn_registry.int_arg name "va" va in
              let root = Fn_registry.int_arg name "base" base in
              let pte_pa = pte_addr name entries ~base:root ~va ~level in
              (* [pte_pa] is a PA; VM code needs the VA for the same entry in
                 the page-table pool window. *)
              let offset = pte_pa - root in
              if offset < 0 || offset >= Allocator.big_size then
                Fn_registry.error
                  "%s: PTE PA 0x%x is outside page-table pool rooted at 0x%x" name
                  pte_pa root;
              Z.of_int (page_table_va_base + offset)
          | args -> Fn_registry.arity_error name 2 (List.length args)
          )
    }
  )

(** [descN(va, base)] treats [base] as the root translation-table PA and
    returns the descriptor stored in the matching level-[N] PTE. *)
let desc_function entries level =
  let name = Printf.sprintf "desc%d" level in
  ( name,
    { Fn_registry.params = ["va"; "base"];
      defaults = [];
      eval =
        (function
          | [va; base] ->
              let addr =
                pte_addr name entries
                  ~base:(Fn_registry.int_arg name "base" base)
                  ~va:(Fn_registry.int_arg name "va" va)
                  ~level
              in
              Z.of_int64 (List.assoc_opt addr entries |> Option.value ~default:0L)
          | args -> Fn_registry.arity_error name 2 (List.length args)
          )
    }
  )

(** [mkdescN(oa=..., ...)] encodes a level-[N] block/page descriptor. *)
let mkdesc_function level =
  let name = Printf.sprintf "mkdesc%d" level in
  ( name,
    { Fn_registry.params = ["oa"; "Valid"; "AF"; "AP"; "DBM"];
      defaults = [("Valid", Z.one); ("AF", Z.one); ("AP", Z.one); ("DBM", Z.zero)];
      eval =
        (function
          | [oa; valid; af; ap; dbm] ->
              Z.of_int64
                (Page_table_desc.make_desc ~level
                   ~oa:(Fn_registry.int_arg name "oa" oa)
                   ~kind:Page_table_ast.Data
                   ~fields:
                     [ {name = "Valid"; value = valid};
                       {name = "AF"; value = af};
                       {name = "AP"; value = ap};
                       {name = "DBM"; value = dbm}
                     ]
                   ()
                )
          | args -> Fn_registry.arity_error name 5 (List.length args)
          )
    }
  )

(** [mkdescN(table=...)] encodes a next-level table descriptor. *)
let mkdesc_table_function level =
  let name = Printf.sprintf "mkdesc%d" level in
  ( name,
    { Fn_registry.params = ["table"];
      defaults = [];
      eval =
        (function
          | [table_addr] ->
              Z.of_int64
                (Page_table_desc.table_descriptor
                   (Fn_registry.int_arg name "table" table_addr)
                )
          | args -> Fn_registry.arity_error name 1 (List.length args)
          )
    }
  )

let functions ~page_table_va_base ~page_table_entries () =
  let levels = [0; 1; 2; 3] in
  [page_function; asid_function]
  @ List.map (pte_function page_table_va_base page_table_entries) levels
  @ List.map (desc_function page_table_entries) levels
  @ List.map mkdesc_function levels
  @ List.map mkdesc_table_function levels
