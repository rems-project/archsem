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

(** Allocation hints and final checks for named address constraints. *)

let size value =
  if Z.sign value <= 0 || not (Z.equal Z.(logand value (pred value)) Z.zero) then
    Litmus.Error.failwith
      "address constraint size must be a positive power of two: %s"
      (Z.to_string value);
  try Z.to_int value
  with Z.Overflow ->
    Litmus.Error.failwith "address constraint size is out of range"

let alignment requests name =
  Hashtbl.find_opt requests name |> Option.value ~default:1

let request_alignment requests name value =
  Hashtbl.replace requests name (max (alignment requests name) value)

let alignment_requests stmts =
  let requests = Hashtbl.create 32 in
  Page_table_ast.iter
    (function
      | Page_table_ast.Aligned {alignment; names} ->
          let alignment = size alignment in
          List.iter (fun name -> request_alignment requests name alignment) names
      | Page_table_ast.Same {size = value; _} -> ignore (size value)
      | _ -> ()
      )
    stmts;
  requests

let check ~state stmts =
  Page_table_ast.iter
    (function
      | Page_table_ast.Aligned {alignment; names} ->
          let alignment = size alignment in
          List.iter
            (fun name ->
               let addr = Eval_state.lookup_addr state name in
               if addr mod alignment <> 0 then
                 Litmus.Error.failwith
                   "symbol %s at 0x%x is not aligned to %d bytes" name addr
                   alignment
             )
            names
      | Page_table_ast.Same {size = value; names} -> (
          let block_size = size value in
          match names with
          | first :: rest ->
              let first_addr = Eval_state.lookup_addr state first in
              List.iter
                (fun name ->
                   let addr = Eval_state.lookup_addr state name in
                   if addr / block_size <> first_addr / block_size then
                     Litmus.Error.failwith
                       "symbols %s (0x%x) and %s (0x%x) are not in the same \
                        %d-byte block"
                        first first_addr name addr block_size
                 )
                rest
          | [] -> ()
        )
      | _ -> ()
      )
    stmts
