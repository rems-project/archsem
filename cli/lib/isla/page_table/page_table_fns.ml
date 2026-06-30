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

(** [page(a)] extracts a 4KB page number from an address. *)
let page_function =
  ( "page",
    function
    | [a] -> Z.extract a 12 36
    | args -> Fn_registry.arity_error "page" 1 (List.length args)
  )

(** [asid(v)] shifts an ASID value into bits [63:48]. *)
let asid_function =
  ( "asid",
    function
    | [v] -> Z.shift_left v 48
    | args -> Fn_registry.arity_error "asid" 1 (List.length args)
  )

let descriptor_field_arg kwargs field_name default =
  { Page_table_ast.name = field_name;
    value = Fn_registry.optional_kwarg field_name default kwargs
  }

(** Find the page-table entry address for [va] at [level]. *)
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
          Fn_registry.error
            "%s: No table descriptor at level %d for VA 0x%x, resolved to be at \
             PA 0x%x in page-table rooted at 0x%x"
             name current_level va addr base
  in
  walk base Page_table_desc.root_level

(** [pteN(va, base)] treats [base] as the root translation-table PA, then
    returns the identity-mapped VA of the matching PTE. *)
let pte_function entries level =
  let name = Printf.sprintf "pte%d" level in
  ( name,
    function
    | [va; base] ->
        let va = Fn_registry.int_arg name "va" va in
        let base = Fn_registry.int_arg name "base" base in
        let pte_pa = pte_addr name entries ~base ~va ~level in
        let offset = pte_pa - base in
        if offset < 0 || offset >= Allocator.big_size then
          Fn_registry.error
            "%s: PTE level %d for VA 0x%x was resolved at PA 0x%x which is \
             outside page-table pool rooted at 0x%x"
             name level va pte_pa base;
        Z.of_int pte_pa
    | args -> Fn_registry.arity_error name 2 (List.length args)
  )

(** [descN(va, base)] treats [base] as the root translation-table PA and
    returns the descriptor stored in the matching level-[N] PTE. *)
let desc_function entries level =
  let name = Printf.sprintf "desc%d" level in
  ( name,
    function
    | [va; base] -> (
        let va = Fn_registry.int_arg name "va" va in
        let base = Fn_registry.int_arg name "base" base in
        let pte_pa = pte_addr name entries ~base ~va ~level in
        match List.assoc_opt pte_pa entries with
        | Some desc -> Z.of_int64 desc
        | None ->
            Fn_registry.error
              "%s: Descriptor level %d for address 0x%x in page-table rooted at \
               0x%x not found at resolved PA 0x%x"
               name level va base pte_pa
      )
    | args -> Fn_registry.arity_error name 2 (List.length args)
  )

(** [mkdescN(oa=..., ...)] encodes a level-[N] block/page descriptor. *)
let eval_desc name level kwargs =
  Fn_registry.check_kwargs name ["oa"; "Valid"; "AF"; "AP"; "DBM"] kwargs;
  let oa = Fn_registry.required_kwarg name "oa" kwargs in
  let fields =
    [ descriptor_field_arg kwargs "Valid" Z.one;
      descriptor_field_arg kwargs "AF" Z.one;
      descriptor_field_arg kwargs "AP" Z.one;
      descriptor_field_arg kwargs "DBM" Z.zero
    ]
  in
  Z.of_int64
    (Page_table_desc.make_descriptor ~level
       ~oa:(Fn_registry.int_arg name "oa" oa)
       ~kind:Page_table_ast.Data ~fields ()
    )

(** [mkdescN(table=...)] encodes a next-level table descriptor. *)
let eval_table_desc name kwargs =
  Fn_registry.check_kwargs name ["table"] kwargs;
  let table_addr = Fn_registry.required_kwarg name "table" kwargs in
  Z.of_int64
    (Page_table_desc.table_descriptor
       (Fn_registry.int_arg name "table" table_addr)
    )

let mkdesc_function level =
  let name = Printf.sprintf "mkdesc%d" level in
  let eval kwargs =
    match (List.mem_assoc "oa" kwargs, List.mem_assoc "table" kwargs) with
    | (true, false) -> eval_desc name level kwargs
    | (false, true) -> eval_table_desc name kwargs
    | _ ->
        Fn_registry.error "%s: Having both oa and table arguments is not allowed"
          name
  in
  (name, eval)

let positional_functions ?page_table_entries () =
  let functions = [page_function; asid_function] in
  match page_table_entries with
  | None -> functions
  | Some page_table_entries ->
      let levels = [0; 1; 2; 3] in
      functions
      @ List.map (pte_function page_table_entries) levels
      @ List.map (desc_function page_table_entries) levels

let keyword_functions : Fn_registry.keyword_fn list =
  let levels = [0; 1; 2; 3] in
  List.map mkdesc_function levels
