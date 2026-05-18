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

(** {1 The expression language} *)

(** An architectural state location, the memory symbol has a size defined by the
    test setup *)
type loc =
  | Reg of int * string
  | Mem of string

(** A comparison atom: Comparing a location to a value or another location. The
    value can either be a number [Z.t] or an unevaluated expression
    [Isla.Term.t], depending on whether the test has been concretized yet *)
type 'a atom =
  | CmpCst of loc * 'a
  | CmpLoc of loc * loc

(** A test final assertion expression *)
type 'a expr =
  | Atom of 'a atom
  | And of 'a expr list
  | Or of 'a expr list
  | Not of 'a expr
  | True
  | False

(** {1 Helper functions} *)

(** {2 Flatten} *)

let get_ands : 'a expr -> 'a expr list = function
  | And exprs -> exprs
  | expr -> [expr]

let get_ors : 'a expr -> 'a expr list = function
  | Or exprs -> exprs
  | expr -> [expr]

let rec flatten : 'a expr -> 'a expr = function
  | And exprs -> And (List.concat (List.map get_ands (List.map flatten exprs)))
  | Or exprs -> Or (List.concat (List.map get_ors (List.map flatten exprs)))
  | Not (Not expr) -> flatten expr
  | Not expr -> Not (flatten expr)
  | expr -> expr

(** {2 Constant map} *)

(** Map a constant to constant function through an [atom] *)
let map_cst_atom (f : 'a -> 'b) : 'a atom -> 'b atom = function
  | CmpCst (loc, cst) -> CmpCst (loc, f cst)
  | CmpLoc (loc, loc') -> CmpLoc (loc, loc')

(** Map a constant to constant function through an [expr] *)
let rec map_cst (f : 'a -> 'b) : 'a expr -> 'b expr = function
  | Atom atom -> Atom (map_cst_atom f atom)
  | And exprs -> And (List.map (map_cst f) exprs)
  | Or exprs -> Or (List.map (map_cst f) exprs)
  | Not exprs -> Not (map_cst f exprs)
  | True -> True
  | False -> False

(** {2 Location map} *)

(** Map a location to location function through an [atom] *)
let map_loc_atom (f : loc -> loc) : 'a atom -> 'a atom = function
  | CmpCst (loc, cst) -> CmpCst (f loc, cst)
  | CmpLoc (loc, loc') -> CmpLoc (f loc, f loc')

(** Map a location to location function through an [expr] *)
let rec map_loc (f : loc -> loc) : 'a expr -> 'a expr = function
  | Atom atom -> Atom (map_loc_atom f atom)
  | And exprs -> And (List.map (map_loc f) exprs)
  | Or exprs -> Or (List.map (map_loc f) exprs)
  | Not exprs -> Not (map_loc f exprs)
  | True -> True
  | False -> False

(** {2 Location enumeration} *)

(** Extracts all locations used in an [atom] *)
let get_locs_atoms : 'a atom -> loc list = function
  | CmpCst (loc, _) -> [loc]
  | CmpLoc (loc, loc') -> [loc; loc']

(** Extracts all locations used in an [expr] *)
let rec get_locs : 'a expr -> loc list = function
  | Atom atom -> get_locs_atoms atom
  | And exprs | Or exprs -> List.concat (List.map get_locs exprs)
  | Not expr -> get_locs expr
  | True | False -> []

(** Extracts all locations used in an [expr] and de-duplicates *)
let get_unique_locs (expr : 'a expr) : loc list =
  List.sort_uniq compare (get_locs expr)

(** {1 Concrete semantic of assertions} *)

(** This module implement the concrete semantics of assertion when values are
    [Z.t] *)
module Checker (Arch : Archsem.Arch) = struct
  open Arch

  (** Lookup a location, expect that it will workout, error must be handled up
      the call stack *)
  let lookup_loc ~resolve_sym (fs : ArchState.t) : loc -> Z.t = function
    | Reg (tid, name) ->
        let regs = ArchState.reg tid fs in
        let reg = Reg.of_string name in
        RegMap.getZ reg regs
    | Mem sym ->
        let (addr, size) = resolve_sym sym in
        MemMap.lookup addr size (ArchState.mem fs)

  let check_atom ~resolve_sym (fs : ArchState.t) : Z.t atom -> bool = function
    | CmpCst (loc, v) -> lookup_loc ~resolve_sym fs loc = v
    | CmpLoc (loc, loc') ->
        lookup_loc ~resolve_sym fs loc = lookup_loc ~resolve_sym fs loc'

  (* Check if a final state satisfies mem_conds *)
  let rec check_assertion ~resolve_sym (fs : ArchState.t) : Z.t expr -> bool
    = function
    | True -> true
    | False -> false
    | And exprs -> List.for_all (check_assertion ~resolve_sym fs) exprs
    | Or exprs -> List.exists (check_assertion ~resolve_sym fs) exprs
    | Not expr -> not (check_assertion ~resolve_sym fs expr)
    | Atom atom -> check_atom ~resolve_sym fs atom
end
