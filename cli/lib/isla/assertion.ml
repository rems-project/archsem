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

(** Boolean expression language for isla litmus test assertions. *)

type loc =
  | Reg of int * string
  | Mem of string

type op =
  | Eq
  | Ne

type atom =
  | CmpCst of loc * op * Z.t
  | CmpLoc of loc * op * loc

type expr =
  | Atom of atom
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | True
  | False

module Testrepr = Litmus.Testrepr

let negate_op = function Eq -> Ne | Ne -> Eq

let negate_atom = function
  | CmpCst (loc, op, value) -> CmpCst (loc, negate_op op, value)
  | CmpLoc (lhs, op, rhs) -> CmpLoc (lhs, negate_op op, rhs)

let rec negate = function
  | Atom atom -> Atom (negate_atom atom)
  | And (a, b) -> Or (negate a, negate b)
  | Or (a, b) -> And (negate a, negate b)
  | Not e -> e
  | True -> False
  | False -> True

let rec to_dnf = function
  | Atom a -> [[a]]
  | True -> [[]]
  | False -> []
  | Not e -> to_dnf (negate e)
  | Or (a, b) -> to_dnf a @ to_dnf b
  | And (a, b) ->
      let da = to_dnf a and db = to_dnf b in
      (* Take the cartesian product of da and db to enumerate all the clauses *)
      List.concat_map (fun ca -> List.map (fun cb -> ca @ cb) db) da
