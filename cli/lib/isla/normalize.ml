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

(** Normalize architecture-specific register aliases in the IR. *)

open Assertion

let register_renames () =
  Otoml.find_or ~default:[] (Litmus.Config.get ())
    (Otoml.get_table_values Otoml.get_string)
    ["isla"; "register_renames"]

let normalize_reg reg =
  match List.assoc_opt reg (register_renames ()) with
  | Some renamed -> renamed
  | None -> reg

let normalize_loc = function
  | Reg (tid, reg) -> Reg (tid, normalize_reg reg)
  | Mem _ as loc -> loc

let normalize_atom = function
  | CmpCst (loc, op, value) -> CmpCst (normalize_loc loc, op, value)
  | CmpLoc (lhs, op, rhs) -> CmpLoc (normalize_loc lhs, op, normalize_loc rhs)

let rec normalize_expr = function
  | Atom atom -> Atom (normalize_atom atom)
  | And (lhs, rhs) -> And (normalize_expr lhs, normalize_expr rhs)
  | Or (lhs, rhs) -> Or (normalize_expr lhs, normalize_expr rhs)
  | Not expr -> Not (normalize_expr expr)
  | True -> True
  | False -> False

let normalize_thread (thread : Ir.thread) =
  { thread with
    init = List.map (fun (reg, value) -> (normalize_reg reg, value)) thread.init
  }

let apply (ir : Ir.t) : Ir.t =
  { ir with
    threads = List.map normalize_thread ir.threads;
    assertion = normalize_expr ir.assertion
  }
