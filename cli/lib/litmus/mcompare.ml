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

(** Convert a list of register state to string format,
    suitable for printing final register states for mcompare *)
let final_regs_to_string (rs : MinState.reg_state list) =
  String.concat " "
    (List.map
       (fun (r : MinState.reg_state) ->
          if r.value >= 0 && r.value < 16 then
            Printf.sprintf "%d:%s=%d;" r.tid r.regname r.value
          else Printf.sprintf "%d:%s=%#x;" r.tid r.regname r.value
        )
       rs
    )

(** Convert a list of memory state to string format,
    suitable for printing final memory states for mcompare *)
let final_mem_to_string (ms : MinState.mem_state list) =
  String.concat " "
    (List.map
       (fun (m : MinState.mem_state) -> Printf.sprintf "[%s]=%d;" m.sym m.value)
       ms
    )

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

let kind_validation (kind : Testrepr.kind) obs_count not_obs_count =
  match kind with
  | Exists -> obs_count > 0
  | Forall -> not_obs_count == 0
  | NotExists -> obs_count == 0

(** Print mcompare compatible output, missing [Condition] and [Hash] for now *)
let print (test : Testrepr.t) states obs_count not_obs_count time =
  Printf.printf "Test %s %s\n" test.name (kind_to_top_string test.kind);
  Printf.printf "States %d\n" (List.length states);
  List.iter
    (fun (regs_state, mems_state) ->
       Printf.printf "%s %s\n"
         (final_regs_to_string regs_state)
         (final_mem_to_string mems_state)
     )
    states;
  if kind_validation test.kind obs_count not_obs_count then Printf.printf "Ok\n"
  else Printf.printf "No\n";
  Printf.printf "Witnesses\n";
  Printf.printf "Positive: %d Negative: %d\n" obs_count not_obs_count;
  (* Skipping Flag and Condition *)
  print_observation test.name obs_count not_obs_count;
  Printf.printf "Time %s %f\n" test.name time
(* Skipping Hash *)
