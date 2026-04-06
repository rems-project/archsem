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

(** AArch64 page table descriptor primitives.

    Pure functions for descriptor encoding, table walk, and entry lookup.
    No dependencies on Term, Function, or Pgtable evaluator. *)

let table_size = 4096

let entry_size = 8

(** {1 Address geometry} *)

let level_shift = function
  | 0 -> 39
  | 1 -> 30
  | 2 -> 21
  | 3 -> 12
  | n -> failwith (Printf.sprintf "pgt_desc: invalid level %d" n)

let va_index va level = (va lsr level_shift level) land 0x1FF

(** {1 Descriptor encoding}

    Attribute bits are stored WITHOUT the type field (bits 1:0).
    Each constructor sets the type:
    - table/page descriptor: bits 1:0 = 0b11
    - block descriptor (L1/L2): bits 1:0 = 0b01 *)

let table_descriptor next_table_pa = next_table_pa land 0x0000FFFFFFFFF000 lor 0x3

let aarch64_data_attrs = 0x440

let aarch64_code_attrs = 0x4C0

let page_descriptor pa attrs = pa land 0x0000FFFFFFFFF000 lor attrs lor 0x3

let block_descriptor pa level attrs =
  let shift = level_shift level in
  let mask = -1 lsl shift in
  pa land mask land 0x0000FFFFFFFFFFFF lor attrs lor 0x1

let make_desc ~level ~oa ~attrs () =
  if level = 3 then page_descriptor oa attrs else block_descriptor oa level attrs

(** {1 Table entry read/write} *)

let write_entry data idx value =
  let offset = idx * entry_size in
  for i = 0 to 7 do
    let byte = (value lsr (i * 8)) land 0xFF in
    Bytes.set data (offset + i) (Char.chr byte)
  done

let read_entry data idx =
  let offset = idx * entry_size in
  let v = ref 0 in
  for i = 7 downto 0 do
    v := (!v lsl 8) lor Char.code (Bytes.get data (offset + i))
  done;
  !v

(** {1 Table walk} *)

type table_data = (int * Bytes.t) list

let lookup_pte_addr ~(table_data : table_data) ~base va level =
  let rec walk cur_base cur_level =
    let idx = va_index va cur_level in
    if cur_level = level then cur_base + (idx * entry_size)
    else
      let tbl = List.assoc cur_base table_data in
      let desc = read_entry tbl idx in
      if desc land 0x3 <> 0x3 then
        failwith
          (Printf.sprintf "pgt_desc: no table descriptor at level %d for VA 0x%x"
             cur_level va
          );
      let next = desc land 0x0000FFFFFFFFF000 in
      walk next (cur_level + 1)
  in
  walk base 0

let lookup_desc_value ~(table_data : table_data) ~base va level =
  let addr = lookup_pte_addr ~table_data ~base va level in
  let tbl_base = addr - (addr mod table_size) in
  let idx = (addr - tbl_base) / entry_size in
  let tbl = List.assoc tbl_base table_data in
  read_entry tbl idx
