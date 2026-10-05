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
let page_function : string * (Z.t list -> Z.t) =
  ( "page",
    function
    | [a] -> Z.extract a 12 36
    | args -> Fn_registry.arity_error "page" 1 (List.length args)
  )

(** [asid(v)] shifts an ASID value into bits [63:48]. *)
let asid_function : string * (Z.t list -> Z.t) =
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
      let desc = Hashtbl.find_opt entries addr |> Option.value ~default:0L in
      match Page_table_desc.table_addr_of_descriptor desc with
      | Some next_table -> walk next_table (current_level + 1)
      | None ->
          Fn_registry.error
            "%s: No table descriptor at level %d for VA 0x%x, resolved to be at \
             PA 0x%x in page-table rooted at 0x%x"
             name current_level va addr base
  in
  walk base Page_table_desc.root_level

(** [pteN(walk)] and [tableN(walk)] use recorded addresses;
    [pteN(va, base)] and [tableN(va, base)] query the current tables. *)
let entry_function ~pte entries level : Fn_registry.positional_fn =
  let name = Printf.sprintf "%s%d" (if pte then "pte" else "table") level in
  let eval : Fn_registry.value list -> int = function
    | [Fn_registry.Walk (walk_name, walk)] -> (
      match List.nth_opt walk level with
      | Some addr -> addr
      | None ->
          Fn_registry.error "%s: table walk %s has no level %d" name walk_name
            level
    )
    | [_] -> Fn_registry.error "%s: expected a table walk" name
    | [va; base] ->
        let va = Fn_registry.int_arg name "va" (Fn_registry.number name va) in
        let base =
          Fn_registry.int_arg name "base" (Fn_registry.number name base)
        in
        let addr = pte_addr name entries ~base ~va ~level in
        if pte && (addr < Allocator.big_size || addr >= 2 * Allocator.big_size)
        then
          Fn_registry.error
            "%s: PTE level %d for VA 0x%x was resolved at PA 0x%x which is \
             outside page-table storage, for root 0x%x"
             name level va addr base;
        addr
    | args ->
        Fn_registry.error "%s: expected 1 or 2 arguments, got %d" name
          (List.length args)
  in
  ( name,
    fun args ->
      let addr = eval args in
      Fn_registry.Num
        (Z.of_int (if pte then addr else Page_table_desc.align_page_addr addr))
  )

let pte_function entries level : Fn_registry.positional_fn =
  entry_function ~pte:true entries level

let table_function entries level : Fn_registry.positional_fn =
  entry_function ~pte:false entries level

(** [descN(va, base)] treats [base] as the root translation-table PA and
    returns the descriptor stored in the matching level-[N] PTE. *)
let desc_function entries level : string * (Z.t list -> Z.t) =
  let name = Printf.sprintf "desc%d" level in
  ( name,
    function
    | [va; base] -> (
        let va = Fn_registry.int_arg name "va" va in
        let base = Fn_registry.int_arg name "base" base in
        let pte_pa = pte_addr name entries ~base ~va ~level in
        match Hashtbl.find_opt entries pte_pa with
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
let eval_desc name level (kwargs : (string * Z.t) list) : Z.t =
  Fn_registry.check_kwargs name ["oa"; "Valid"; "AF"; "AP"; "DBM"; "nG"] kwargs;
  let oa = Fn_registry.required_kwarg name "oa" kwargs in
  let fields =
    [ descriptor_field_arg kwargs "Valid" Z.one;
      descriptor_field_arg kwargs "AF" Z.one;
      descriptor_field_arg kwargs "AP" Z.one;
      descriptor_field_arg kwargs "DBM" Z.zero;
      descriptor_field_arg kwargs "nG" Z.zero
    ]
  in
  Z.of_int64
    (Page_table_desc.make_descriptor ~level
       ~oa:(Fn_registry.int_arg name "oa" oa)
       ~kind:Page_table_ast.Data ~fields ()
    )

(** [mkdescN(table=...)] encodes a next-level table descriptor. *)
let eval_table_desc name (kwargs : (string * Z.t) list) : Z.t =
  Fn_registry.check_kwargs name ["table"; "APTable"] kwargs;
  let table_addr = Fn_registry.required_kwarg name "table" kwargs in
  let fields = [descriptor_field_arg kwargs "APTable" Z.zero] in
  Z.of_int64
    (Page_table_desc.table_descriptor ~fields
       (Fn_registry.int_arg name "table" table_addr)
    )

let mkdesc_function level : string * ((string * Z.t) list -> Z.t) =
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

let check_unsigned name arg bits value =
  if Z.sign value < 0 || Z.numbits value > bits then
    Fn_registry.error "%s: argument %s does not fit in %d bits" name arg bits

(** [ttbr(asid=..., base=...)] and [ttbr(vmid=..., base=...)] combine a
    concrete translation-table root PA with its 16-bit address-space ID. *)
let ttbr_function : string * ((string * Z.t) list -> Z.t) =
  let name = "ttbr" in
  let eval kwargs =
    Fn_registry.check_kwargs name ["asid"; "vmid"; "base"] kwargs;
    let base = Fn_registry.required_kwarg name "base" kwargs in
    let (id_name, id) =
      match (List.assoc_opt "asid" kwargs, List.assoc_opt "vmid" kwargs) with
      | (Some id, None) -> ("asid", id)
      | (None, Some id) -> ("vmid", id)
      | _ -> Fn_registry.error "%s: expected exactly one of asid or vmid" name
    in
    check_unsigned name id_name 16 id;
    check_unsigned name "base" 48 base;
    if not (Z.equal (Z.extract base 0 12) Z.zero) then
      Fn_registry.error "%s: argument base must be 4KB aligned" name;
    Z.((id lsl 48) lor base)
  in
  (name, eval)

let positional_functions ~state : Fn_registry.positional_fn list =
  let functions =
    List.map
      (fun (name, eval) ->
         ( name,
           fun args ->
             Fn_registry.Num (eval (List.map (Fn_registry.number name) args))
         )
       )
      [page_function; asid_function]
  in
  match state.Eval_state.page_table with
  | None -> functions
  | Some entries ->
      let levels = [0; 1; 2; 3] in
      functions
      @ List.map (pte_function entries) levels
      @ List.map
          (fun level ->
             let (name, eval) = desc_function entries level in
             ( name,
               fun args ->
                 Fn_registry.Num (eval (List.map (Fn_registry.number name) args))
             )
           )
          levels
      @ List.map (table_function entries) levels

let keyword_functions : Fn_registry.keyword_fn list =
  let levels = [0; 1; 2; 3] in
  List.map
    (fun (name, eval) ->
       ( name,
         fun kwargs ->
           let args =
             List.map (fun (k, v) -> (k, Fn_registry.number name v)) kwargs
           in
           Fn_registry.Num (eval args)
       )
     )
    (ttbr_function :: List.map mkdesc_function levels)
