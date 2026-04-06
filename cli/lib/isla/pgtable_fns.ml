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

(** Page table query functions: pteN, descN, mkdescN, page, asid.
    Delegates descriptor lookups to {!Pgtable_desc}. *)

let pgt_fn_for_level prefix level ~mk_eval =
  let name = Printf.sprintf "%s%d" prefix level in
  (name, {Fn_registry.params = ["va"; "base"]; eval = mk_eval name level})

let pgt_functions : (string * Fn_registry.fn_spec) list =
  let levels = [0; 1; 2; 3] in
  [ ( "page",
      { Fn_registry.params = ["a"];
        eval =
          (fun _ -> function
             | [a] ->
                 Z.logand (Z.shift_right a 12)
                   (Z.sub (Z.shift_left Z.one 36) Z.one)
             | _ -> Fn_registry.arity_error "page" 1
             )
      }
    )
  ]
  @ List.map
      (pgt_fn_for_level "pte" ~mk_eval:(fun name level ->
         fun td -> function
           | [va; base] ->
               Z.of_int
                 (Pgtable_desc.lookup_pte_addr ~table_data:td
                    ~base:(Z.to_int base) (Z.to_int va) level
                 )
           | _ -> Fn_registry.arity_error name 2
       )
      )
      levels
  @ List.map
      (pgt_fn_for_level "desc" ~mk_eval:(fun name level ->
         fun td -> function
           | [va; base] ->
               Z.of_int
                 (Pgtable_desc.lookup_desc_value ~table_data:td
                    ~base:(Z.to_int base) (Z.to_int va) level
                 )
           | _ -> Fn_registry.arity_error name 2
       )
      )
      levels
  @ List.concat_map
      (fun level ->
         let name = Printf.sprintf "mkdesc%d" level in
         [ ( name,
             { Fn_registry.params = ["oa"];
               eval =
                 (fun _ -> function
                    | [oa] ->
                        Z.of_int
                          (Pgtable_desc.make_desc ~level ~oa:(Z.to_int oa)
                             ~attrs:Pgtable_desc.aarch64_data_attrs ()
                          )
                    | _ -> Fn_registry.arity_error name 1
                    )
             }
           );
           ( name ^ "_table",
             { Fn_registry.params = ["table"];
               eval =
                 (fun _ -> function
                    | [table_addr] ->
                        Z.of_int
                          (Pgtable_desc.table_descriptor (Z.to_int table_addr))
                    | _ -> Fn_registry.arity_error (name ^ "_table") 1
                    )
             }
           )
         ]
       )
      levels

let misc_functions : (string * Fn_registry.fn_spec) list =
  [ ( "asid",
      { Fn_registry.params = ["v"];
        eval =
          (fun _ -> function
             | [v] -> Z.shift_left v 48 | _ -> Fn_registry.arity_error "asid" 1
             )
      }
    )
  ]

let functions : (string * Fn_registry.fn_spec) list =
  pgt_functions @ misc_functions
