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

(** An architectural state location.

    Symbolic memory locations have their size defined by the test setup.
    Addressed memory locations carry an address term, whose concrete type
    depends on whether the assertion has been evaluated yet. *)
type 'a loc =
  | Reg of int * string
  | Mem of string
  | MemAddr of 'a

(** A comparison atom: Comparing a location to a value or another location. The
    value can either be a number [Z.t] or an unevaluated expression
    [Isla.Term.t], depending on whether the test has been concretized yet *)
type 'a atom =
  | CmpCst of 'a loc * 'a
  | CmpLoc of 'a loc * 'a loc

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

(** Map an address term through a [loc] *)
let map_cst_loc (f : 'a -> 'b) : 'a loc -> 'b loc = function
  | Reg (thread, reg) -> Reg (thread, reg)
  | Mem sym -> Mem sym
  | MemAddr addr -> MemAddr (f addr)

(** Map term-valued assertion payloads through an [atom].

    This maps both right-hand-side constants and [MemAddr] address terms. *)
let map_cst_atom (f : 'a -> 'b) : 'a atom -> 'b atom = function
  | CmpCst (loc, cst) -> CmpCst (map_cst_loc f loc, f cst)
  | CmpLoc (loc, loc') -> CmpLoc (map_cst_loc f loc, map_cst_loc f loc')

(** Map term-valued assertion payloads through an [expr] *)
let rec map_cst (f : 'a -> 'b) : 'a expr -> 'b expr = function
  | Atom atom -> Atom (map_cst_atom f atom)
  | And exprs -> And (List.map (map_cst f) exprs)
  | Or exprs -> Or (List.map (map_cst f) exprs)
  | Not exprs -> Not (map_cst f exprs)
  | True -> True
  | False -> False

(** {2 Location map} *)

(** Map a location to location function through an [atom] *)
let map_loc_atom (f : 'a loc -> 'a loc) : 'a atom -> 'a atom = function
  | CmpCst (loc, cst) -> CmpCst (f loc, cst)
  | CmpLoc (loc, loc') -> CmpLoc (f loc, f loc')

(** Map a location to location function through an [expr] *)
let rec map_loc (f : 'a loc -> 'a loc) : 'a expr -> 'a expr = function
  | Atom atom -> Atom (map_loc_atom f atom)
  | And exprs -> And (List.map (map_loc f) exprs)
  | Or exprs -> Or (List.map (map_loc f) exprs)
  | Not exprs -> Not (map_loc f exprs)
  | True -> True
  | False -> False

(** {2 Location enumeration} *)

(** Extracts all locations used in an [atom] *)
let get_locs_atoms : 'a atom -> 'a loc list = function
  | CmpCst (loc, _) -> [loc]
  | CmpLoc (loc, loc') -> [loc; loc']

(** Extracts all locations used in an [expr] *)
let rec get_locs : 'a expr -> 'a loc list = function
  | Atom atom -> get_locs_atoms atom
  | And exprs | Or exprs -> List.concat (List.map get_locs exprs)
  | Not expr -> get_locs expr
  | True | False -> []

(** Extracts all locations used in an [expr] and de-duplicates *)
let get_unique_locs (expr : 'a expr) : 'a loc list =
  List.sort_uniq compare (get_locs expr)

(** {1 Concrete semantic of assertions} *)

(** This module implement the concrete semantics of assertion when values are
    [Z.t] *)
module Checker (Arch : Archsem.Arch) = struct
  open Arch

  let pte_address_size = 8

  (** Lookup a location, expect that it will workout, error must be handled up
      the call stack *)
  let int_of_addr addr =
    if Z.sign addr < 0 then failwith "Memory address is negative";
    match Z.to_int addr with
    | addr -> addr
    | exception Z.Overflow -> failwith "Memory address is too large"

  let lookup_loc ~lookup_addr (fs : ArchState.t) : Z.t loc -> Z.t = function
    | Reg (tid, name) ->
        let regs = ArchState.reg tid fs in
        let arch_name = Config.get_reg_rename_or name in
        let reg = Reg.of_string arch_name in
        RegMap.getZ reg regs
    | Mem sym ->
        let (addr, size) = lookup_addr sym in
        MemMap.lookup addr size (ArchState.mem fs)
    | MemAddr addr ->
        MemMap.lookup (int_of_addr addr) pte_address_size (ArchState.mem fs)

  let check_atom ~lookup_addr (fs : ArchState.t) : Z.t atom -> bool = function
    | CmpCst (loc, v) -> lookup_loc ~lookup_addr fs loc = v
    | CmpLoc (loc, loc') ->
        lookup_loc ~lookup_addr fs loc = lookup_loc ~lookup_addr fs loc'

  (* Check if a final state satisfies mem_conds *)
  let rec check_assertion ~lookup_addr (fs : ArchState.t) : Z.t expr -> bool
    = function
    | True -> true
    | False -> false
    | And exprs -> List.for_all (check_assertion ~lookup_addr fs) exprs
    | Or exprs -> List.exists (check_assertion ~lookup_addr fs) exprs
    | Not expr -> not (check_assertion ~lookup_addr fs expr)
    | Atom atom -> check_atom ~lookup_addr fs atom
end
