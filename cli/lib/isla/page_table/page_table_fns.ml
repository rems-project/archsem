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

(** [mkdescN(oa=..., ...)] encodes a level-[N] block/page descriptor. *)
let make_desc_function level =
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
let make_table_desc_function level =
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

let functions =
  let levels = [0; 1; 2; 3] in
  [page_function; asid_function]
  @ List.map make_desc_function levels
  @ List.map make_table_desc_function levels
