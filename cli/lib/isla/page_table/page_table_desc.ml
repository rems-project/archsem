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

(** AArch64 page table descriptor primitives.

    Pure functions for descriptor encoding and table entry read/write. *)

let table_size = Allocator.page_size

let align_page_addr addr = addr - (addr mod Allocator.page_size)

let entry_size = 8

let root_level = 0

let last_level = 3

let aarch64_data_attrs = 0x440L

let aarch64_code_attrs = 0x4C0L

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

let descriptor_field_by_name name =
  List.find_opt (fun field -> field.name = name) descriptor_fields

(** Bit shift of the VA index for a 4KB AArch64 translation-table level. *)
let level_shift = function
  | 0 -> 39
  | 1 -> 30
  | 2 -> 21
  | 3 -> 12
  | n -> Printf.ksprintf invalid_arg "page_table_desc: invalid level %d" n

(** Extract the 9-bit table index for [va] at [level]. *)
let va_index va level = (va lsr level_shift level) land 0x1FF

(** {1 Descriptor values}

    Attribute bits are stored without the type field (bits 1:0). *)

let addr_mask = 0x0000FFFFFFFFF000L

let low_attr_mask = 0xFFFL

let desc_type_mask = 0x3L

let attr_mask = Int64.logand low_attr_mask (Int64.lognot desc_type_mask)

let require_in_mask name mask value =
  if Int64.logand value (Int64.lognot mask) <> 0L then
    Printf.ksprintf failwith
      "page_table_desc: %s 0x%Lx is not contained in mask 0x%Lx" name value mask

let require_addr_in_mask name addr =
  let addr = Int64.of_int addr in
  require_in_mask name addr_mask addr;
  addr

(** Extract the output address from a table, block, or page descriptor. *)
let addr_of_descriptor desc = Int64.to_int (Int64.logand desc addr_mask)

let descriptor_valid desc = Int64.logand desc 0x1L <> 0L

(** Return the next table address when [desc] is a table descriptor. *)
let table_addr_of_descriptor desc =
  let attrs = Int64.logand desc low_attr_mask in
  if attrs = 0x3L then Some (addr_of_descriptor desc) else None

(** Encode a descriptor that points to the next-level table page. *)
let table_descriptor next_table_pa =
  let next_table_pa = require_addr_in_mask "next_table_pa" next_table_pa in
  Int64.logor next_table_pa 0x3L

(** Encode a level-3 page descriptor. *)
let page_descriptor pa attrs =
  let pa = require_addr_in_mask "pa" pa in
  require_in_mask "attrs" attr_mask attrs;
  Int64.logor (Int64.logor pa attrs) 0x3L

let set_descriptor_field desc field value =
  let mask =
    Int64.shift_left (Int64.pred (Int64.shift_left 1L field.width)) field.lsb
  in
  let value = Int64.shift_left (Int64.of_int value) field.lsb in
  Int64.logor (Int64.logand desc (Int64.lognot mask)) value

let descriptor_field_value field (value : Z.t) =
  let value =
    try Ok (Z.to_int value)
    with Z.Overflow ->
      Error (Printf.sprintf "descriptor field %s is out of range" field.name)
  in
  match value with
  | Error _ as err -> err
  | Ok value ->
      let max_value = 1 lsl field.width in
      if value < 0 || value >= max_value then
        Error
          (Printf.sprintf "descriptor field %s value %d does not fit in %d bits"
             field.name value field.width
          )
      else Ok value

let apply_descriptor_field desc (name, value) =
  match descriptor_field_by_name name with
  | None -> Error (Printf.sprintf "unsupported descriptor field: %s" name)
  | Some field -> (
    match descriptor_field_value field value with
    | Error _ as err -> err
    | Ok value -> Ok (set_descriptor_field desc field value)
  )

let page_descriptor_with_fields pa attrs fields =
  let desc = page_descriptor pa attrs in
  List.fold_left
    (fun desc field ->
       match desc with
       | Error _ as err -> err
       | Ok desc -> apply_descriptor_field desc field
     )
    (Ok desc) fields

(** {1 Entry encoding}

    Each table entry stores one descriptor value as a 64-bit little-endian word. *)

(** Read one descriptor entry from a table page. *)
let read_entry data idx =
  let offset = idx * entry_size in
  Bytes.get_int64_le data offset

(** Write one descriptor entry into a table page. *)
let write_entry data idx value =
  let offset = idx * entry_size in
  Bytes.set_int64_le data offset value
