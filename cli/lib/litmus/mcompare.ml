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

(** Functions for displaying mcompare-compatible output *)

let loc_to_string (loc : Assertion.loc) =
  match loc with
  | Reg (tid, reg) -> Printf.sprintf "%d:%s" tid reg
  | Mem sym -> Printf.sprintf "[%s]" sym

(** Print a state element in herd style e.g. [0:R0=4] *)
let print_state_atom ((loc : Assertion.loc), value) =
  Printf.printf "%s=%s; " (loc_to_string loc) (Toml.Numbers.int_to_string value)

(** Print a partial state in herd style e.g. [0:R0=4; [x]=5] *)
let print_state (state : (Assertion.loc * Z.t) list) =
  List.iter print_state_atom state;
  Printf.printf "\n"

(** Print observation line:
    [Observation <test name> <Always/Sometimes/Never> <obs-count> <not-obs-count>] *)
let print_observation test_name obs_count not_obs_count =
  Printf.printf "Observation %s %s %d %d\n" test_name
    ( if obs_count = 0 then "Never"
      else if not_obs_count = 0 then "Always"
      else "Sometimes"
    )
    obs_count not_obs_count

let kind_to_top_string : Testrepr.kind -> string = function
  | Exists -> "Allowed"
  | Forall -> "Forall"
  | NotExists -> "Forbidden"

let kind_to_cond_string : Testrepr.kind -> string = function
  | Exists -> "exists"
  | Forall -> "forall"
  | NotExists -> "notexists"

let kind_validation (kind : Testrepr.kind) obs_count not_obs_count =
  match kind with
  | Exists -> obs_count > 0
  | Forall -> not_obs_count == 0
  | NotExists -> obs_count == 0

let assertion_atom_to_string : Z.t Assertion.atom -> string = function
  | CmpCst (loc, cst) ->
      Printf.sprintf "%s=%s" (loc_to_string loc) (Toml.Numbers.int_to_string cst)
  | CmpLoc (loc, loc') ->
      Printf.sprintf "%s=%s" (loc_to_string loc) (loc_to_string loc')

(* TODO: less dumb pretty printing *)
let rec assertion_to_string : Z.t Assertion.expr -> string = function
  | Atom atom -> assertion_atom_to_string atom
  | And exprs ->
      exprs
      |> List.map assertion_to_string
      |> String.concat " /\\ " |> Printf.sprintf "(%s)"
  | Or exprs ->
      exprs
      |> List.map assertion_to_string
      |> String.concat " \\/ " |> Printf.sprintf "(%s)"
  | Not expr -> Printf.sprintf "not %s" (assertion_to_string expr)
  | True -> "true"
  | False -> "false"

let print_condition name kind cond =
  Printf.printf "Condition %s %s %s\n" name (kind_to_cond_string kind)
    (assertion_to_string cond)

(** Print mcompare compatible output, missing [Condition] and [Hash] for now *)
let print (test : Testrepr.t) states obs_count not_obs_count time =
  Printf.printf "Test %s %s\n" test.name (kind_to_top_string test.kind);
  Printf.printf "States %d\n" (List.length states);
  List.iter print_state states;
  if kind_validation test.kind obs_count not_obs_count then Printf.printf "Ok\n"
  else Printf.printf "No\n";
  Printf.printf "Witnesses\n";
  Printf.printf "Positive: %d Negative: %d\n" obs_count not_obs_count;
  print_condition test.name test.kind test.final;
  (* Skipping Flag *)
  print_observation test.name obs_count not_obs_count;
  Printf.printf "Time %s %.3f\n" test.name time
(* Skipping Hash *)
