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

(** Functions for displaying mcompare-compatible output *)

(* Convert a list of register state to string format, 
  suitable for printing final register states for mcompare *)
let final_regs_to_string (rs : MinState.reg_state list) =
  String.concat " "
    (List.map
       (fun (r : MinState.reg_state) ->
          Printf.sprintf "%d:%s=%d;" r.tid r.regname r.value
        )
       rs
    )

(* Convert a list of memory state to string format, 
  suitable for printing final memory states for mcompare *)
let final_mem_to_string (ms : MinState.mem_state list) =
  String.concat " "
    (List.map
       (fun (m : MinState.mem_state) -> Printf.sprintf "[%s]=%d;" m.sym m.value)
       ms
    )

(* Print how often an outcome occurs, part of the required Mcompare output *)
let outcome_freq_to_string yes_freq no_freq =
  if yes_freq = 0 then "Never" else if no_freq = 0 then "Always" else "Sometimes"

(* Return string of format: Observation <test name> <string freq> <true count> <false count>.
  which is required for Mcompare output*)
let test_observation_stats_to_string obs_count not_obs_count test_name =
  Printf.sprintf "Observation %s %s %d %d" test_name
    (outcome_freq_to_string obs_count not_obs_count)
    obs_count not_obs_count

module Make (Arch : Archsem.Arch) = struct
  open Arch
  module MinimiseState = MinState.Make (Arch)
  module RunnerUtils = Runner_utils.Make (Arch)

  (* Get the number of states which satisfy at least one condition in conds *)
  let get_obs_count
        (conds : (Testrepr.thread_cond list * Testrepr.mem_cond list) list)
        (state_list : ArchState.t list)
    =
    List.length state_list
    - List.length
        (List.fold_left
           (fun unmatched_state_list (cond, mem_cond) ->
              List.filter
                (fun fs ->
                   not
                     (RunnerUtils.check_outcome fs cond
                     && RunnerUtils.check_mem_outcome fs mem_cond
                     )
                 )
                unmatched_state_list
            )
           state_list conds
        )

  (* Print observation statistics for Mcompare. The format is:
    Ok/No <Optional extra detail>
    Observation <test_name> Always/Sometimes/Never <#observed> <#not_observed> *)
  let observation_statistics_string
        (conds : (Testrepr.thread_cond list * Testrepr.mem_cond list) list)
        (checking_for_positive : bool)
        (state_list : ArchState.t list)
        (test_name : string) : string
    =
    let (matched_msg, not_matched_msg) =
      if checking_for_positive then ("Ok", "No (\"allowed\" not found)")
      else ("No (\"not allowed\" found)", "Ok")
    in
    let obs_count = get_obs_count conds state_list in
    let msg = if obs_count > 0 then matched_msg else not_matched_msg in
    msg ^ "\n"
    ^ test_observation_stats_to_string obs_count
        (List.length state_list - obs_count)
        test_name

  (* Top-level function to call for mcompare-compatible output *)
  let print_final_states
        (observable : (Testrepr.thread_cond list * Testrepr.mem_cond list) list)
        (unobservable : (Testrepr.thread_cond list * Testrepr.mem_cond list) list)
        (final_states : ArchState.t list)
        (test_name : string) : string
    =
    let conds = observable @ unobservable in
    let unique_cond = MinimiseState.get_unique_conds_ignoring_value conds in
    let minimised_fs = MinimiseState.minimise_states unique_cond final_states in
    let unique_minimised_fs = List.sort_uniq compare minimised_fs in

    (* Print number of distinct observed states *)
    let states_count_part =
      Printf.sprintf "States %d\n" (List.length unique_minimised_fs)
    in
    (* Print each distinct observable state *)
    let state_list_part =
      if conds <> [] then
        List.map
          (fun (regs_state, mems_state) ->
             Printf.sprintf "%s %s\n"
               (final_regs_to_string regs_state)
               (final_mem_to_string mems_state)
           )
          unique_minimised_fs
        |> String.concat ""
      else ""
    in
    let observation_part =
      if
        (* Print statistics about the condition(s) that we did and didn't want to observe *)
        observable <> []
      then observation_statistics_string observable true final_states test_name
      else if unobservable <> [] then
        observation_statistics_string unobservable false final_states test_name
      else "ERROR: no conditions to observe"
    in

    states_count_part ^ state_list_part ^ observation_part
end
