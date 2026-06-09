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

(** Page-table query functions: page, asid, pteN, descN, mkdescN,
    mkdescN_table.

    mkdescN accepts optional descriptor field overrides for the stage-1 fields
    used by the VM tests: Valid, AF, AP, and DBM. *)

type page_table_entries = (int * int64) list

let function_error name fmt =
  Printf.ksprintf (Litmus.Error.failwith "function: %s: %s" name) fmt

let int_arg name arg value =
  try Z.to_int value
  with Z.Overflow -> function_error name "argument %s is too large" arg

let descriptor_at entries addr =
  List.assoc_opt addr entries |> Option.value ~default:0L

let validate_level name level =
  if level < Page_table_desc.root_level || level > Page_table_desc.last_level then
    function_error name "invalid level %d" level

type descriptor_field =
  { name : string;
    lsb : int;
    width : int
  }

let descriptor_fields =
  [ {name = "Valid"; lsb = 0; width = 1};
    {name = "AF"; lsb = 10; width = 1};
    {name = "AP"; lsb = 6; width = 2};
    {name = "DBM"; lsb = 51; width = 1}
  ]

let descriptor_field_params =
  "oa" :: List.map (fun field -> field.name) descriptor_fields

let descriptor_field_defaults =
  [("Valid", Z.one); ("AF", Z.one); ("AP", Z.one); ("DBM", Z.zero)]

let set_descriptor_field function_name desc field value =
  let value = int_arg function_name field.name value in
  let max_value = 1 lsl field.width in
  if value < 0 || value >= max_value then
    function_error function_name "argument %s does not fit in %d bits" field.name
      field.width;
  let mask =
    Int64.shift_left (Int64.pred (Int64.shift_left 1L field.width)) field.lsb
  in
  let value = Int64.shift_left (Int64.of_int value) field.lsb in
  Int64.logor (Int64.logand desc (Int64.lognot mask)) value

let make_desc name level oa field_values =
  let desc =
    Page_table_desc.make_desc ~level ~oa:(int_arg name "oa" oa)
      ~attrs:Page_table_desc.aarch64_data_attrs ()
  in
  match field_values with
  | [] -> desc
  | _ when List.length field_values = List.length descriptor_fields ->
      List.fold_left2
        (fun desc field value -> set_descriptor_field name desc field value)
        desc descriptor_fields field_values
  | _ -> Fn_registry.arity_error name 1 (1 + List.length field_values)

let pte_addr name entries ~base ~va ~level =
  validate_level name level;
  let rec walk table current_level =
    let index = Page_table_desc.va_index va current_level in
    let addr = table + (index * Page_table_desc.entry_size) in
    if current_level = level then addr
    else
      let desc = descriptor_at entries addr in
      match Page_table_desc.table_addr_of_descriptor desc with
      | Some next_table -> walk next_table (current_level + 1)
      | None ->
          function_error name "no table descriptor at level %d for VA 0x%x"
            current_level va
  in
  walk base Page_table_desc.root_level

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

let pte_function entries level =
  let name = Printf.sprintf "pte%d" level in
  ( name,
    { Fn_registry.params = ["va"; "base"];
      defaults = [];
      eval =
        (function
          | [va; base] ->
              Z.of_int
                (pte_addr name entries ~base:(int_arg name "base" base)
                   ~va:(int_arg name "va" va) ~level
                )
          | args -> Fn_registry.arity_error name 2 (List.length args)
          )
    }
  )

let desc_function entries level =
  let name = Printf.sprintf "desc%d" level in
  ( name,
    { Fn_registry.params = ["va"; "base"];
      defaults = [];
      eval =
        (function
          | [va; base] ->
              let addr =
                pte_addr name entries ~base:(int_arg name "base" base)
                  ~va:(int_arg name "va" va) ~level
              in
              Z.of_int64 (descriptor_at entries addr)
          | args -> Fn_registry.arity_error name 2 (List.length args)
          )
    }
  )

let mkdesc_function level =
  let name = Printf.sprintf "mkdesc%d" level in
  ( name,
    { Fn_registry.params = descriptor_field_params;
      defaults = descriptor_field_defaults;
      eval =
        (function
          | [oa] -> Z.of_int64 (make_desc name level oa [])
          | oa :: field_values -> Z.of_int64 (make_desc name level oa field_values)
          | args -> Fn_registry.arity_error name 1 (List.length args)
          )
    }
  )

let mkdesc_table_function level =
  let name = Printf.sprintf "mkdesc%d_table" level in
  ( name,
    { Fn_registry.params = ["table"];
      defaults = [];
      eval =
        (function
          | [table_addr] ->
              Z.of_int64
                (Page_table_desc.table_descriptor
                   (int_arg name "table" table_addr)
                )
          | args -> Fn_registry.arity_error name 1 (List.length args)
          )
    }
  )

let functions ?(page_table_entries = []) () =
  let levels = [0; 1; 2; 3] in
  [page_function; asid_function]
  @ List.map (pte_function page_table_entries) levels
  @ List.map (desc_function page_table_entries) levels
  @ List.map mkdesc_function levels
  @ List.map mkdesc_table_function levels
