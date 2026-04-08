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

(** Litmus test runner. *)

(** {1 Types} *)

type test_result =
  | Expected  (** Outcome matched test expectations *)
  | Unexpected  (** Outcome did not match test expectations *)
  | ModelError  (** Model produced errors during execution *)
  | NoBehaviour  (** Model produces no behaviours (model bug) *)
  | ParseError  (** Parser or configuration error *)

(** {1 Display Helpers} *)
let rec string_of_regval_gen : Archsem.RegValGen.t -> string = function
  | Number z -> Printf.sprintf "0x%s" (Z.format "%x" z)
  | String s -> Printf.sprintf "\"%s\"" s
  | Array vs ->
      Printf.sprintf "[%s]" (String.concat ", " (List.map string_of_regval_gen vs))
  | Struct fields ->
      Printf.sprintf "{ %s }"
        (String.concat ", "
           (List.map
              (fun (k, v) -> Printf.sprintf "%s = %s" k (string_of_regval_gen v))
              fields
           )
        )

let req_to_string (reg, req) =
  let (op, v) =
    match req with Testrepr.ReqEq v -> ("=", v) | Testrepr.ReqNe v -> ("!=", v)
  in
  Printf.sprintf "%s%s%s" reg op (string_of_regval_gen v)

let cond_to_string cond =
  List.map
    (fun (tid, reqs) ->
       Printf.sprintf "%d:{%s}" tid
         (String.concat "," (List.map req_to_string reqs))
     )
    cond
  |> String.concat " "

let mem_cond_to_string mem_reqs =
  List.map
    (fun (mc : Testrepr.mem_cond) ->
       let (op, value) =
         match mc.req with
         | Testrepr.MemEq value -> ("=", value)
         | Testrepr.MemNe value -> ("!=", value)
       in
       Printf.sprintf "*0x%x[%d]%s0x%s" mc.addr mc.size op (Z.format "%x" value)
     )
    mem_reqs
  |> String.concat " "

let result_to_string = function
  | Expected -> Terminal.green ^ "EXPECTED" ^ Terminal.reset
  | Unexpected -> Terminal.yellow ^ "UNEXPECTED" ^ Terminal.reset
  | ModelError -> Terminal.red ^ "MODEL ERROR" ^ Terminal.reset
  | NoBehaviour -> Terminal.red ^ "NO BEHAVIOUR" ^ Terminal.reset
  | ParseError -> Terminal.red ^ "PARSE ERROR" ^ Terminal.reset

let outcome_freq_to_string yes_freq no_freq =
  if yes_freq = 0 then "Never" else if no_freq = 0 then "Always" else "Sometimes"

(* Return string of format: Observation <test name> <string freq> <true count> <false count>*)
let test_observation_stats_to_string obs_count not_obs_count test_name =
  Printf.sprintf "Observation %s %s %d %d" test_name
    (outcome_freq_to_string obs_count not_obs_count)
    obs_count not_obs_count

module Make (Arch : Archsem.Arch) = struct
  open Arch
  module AS = ToArchState.Make (Arch)
  module MinimiseState = MinState.Make (Arch)

  let check_outcome (fs : ArchState.t) (cond : Testrepr.thread_cond list) : bool =
    List.for_all
      (fun (tid, reqs) ->
         let regs = ArchState.reg tid fs in
         List.for_all
           (fun (name, req) ->
              let reg = Reg.of_string name in
              match RegMap.get_opt reg regs with
              | None ->
                  failwith
                    ("[[outcome]] register not found in final state: " ^ name)
              | Some rv -> (
                match req with
                | Testrepr.ReqEq exp -> rv = RegVal.of_gen reg exp
                | Testrepr.ReqNe exp -> rv = RegVal.of_gen reg exp
              )
            )
           reqs
       )
      cond

  let check_mem_outcome (fs : ArchState.t) (mem_conds : Testrepr.mem_cond list) :
    bool
    =
    let mem = ArchState.mem fs in
    List.for_all
      (fun (mc : Testrepr.mem_cond) ->
         match MemMap.lookup_opt mc.addr mc.size mem with
         | None ->
             failwith
               (Printf.sprintf "[[outcome]] memory not found at 0x%x" mc.addr)
         | Some actual -> (
           match mc.req with
           | Testrepr.MemEq expected -> Z.equal actual expected
           | Testrepr.MemNe expected -> not (Z.equal actual expected)
         )
       )
      mem_conds

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
                   not (check_outcome fs cond && check_mem_outcome fs mem_cond)
                 )
                unmatched_state_list
            )
           state_list conds
        )

  (* Print observation statistics. The format is:
    Ok/No <optional extra detail>
    Observation <test_name> Always/Sometimes/Never <#times_test_cond_observed> <#times_test_cond_not_observed> *)
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

  let run_executions print_final_states model init fuel term test =
    let msgs = ref [] in
    let msg s = msgs := s :: !msgs in
    let results = model fuel term init in

    let observable =
      List.filter_map
        (function Testrepr.Observable (c, mc) -> Some (c, mc) | _ -> None)
        test.Testrepr.finals
    in
    let unobservable =
      List.filter_map
        (function Testrepr.Unobservable (c, mc) -> Some (c, mc) | _ -> None)
        test.Testrepr.finals
    in

    let errors =
      List.filter_map
        (function ArchModel.Res.Error e -> Some e | _ -> None)
        results
    in
    let final_states =
      List.filter_map
        (function ArchModel.Res.FinalState fs -> Some fs | _ -> None)
        results
    in
    let flags =
      List.filter_map
        (function ArchModel.Res.Flagged x -> Some x | _ -> None)
        results
    in

    (* If the print-final-states flag is set, print all observable states and statistics *)
    if print_final_states then (
      let conds = observable @ unobservable in
      let unique_cond = MinimiseState.get_unique_conds_ignoring_value conds in
      let minimised_fs = MinimiseState.minimise_states unique_cond final_states in
      let unique_minimised_fs =
        List.sort_uniq MinimiseState.compare_minimised_states minimised_fs
      in

      (* Print number of distinct observed states *)
      msg (Printf.sprintf "States %d" (List.length unique_minimised_fs));
      (* Print each distinct observable state *)
      if conds <> [] then (
        List.iter
          (fun (regs_state, mems_state) ->
             msg
               (Printf.sprintf "%s %s"
                  (MinimiseState.final_regs_to_string regs_state)
                  (MinimiseState.final_mem_to_string mems_state)
               )
           )
          unique_minimised_fs;
        (* Print statistics about the condition(s) that we did and didn't want to observe *)
        if observable <> [] then
          msg
            (observation_statistics_string observable true final_states test.name)
        else if unobservable <> [] then
          msg
            (observation_statistics_string unobservable false final_states
               test.name
            )
        else msg "ERROR: no conditions to observe"
      )
    );

    List.iter
      (fun e ->
         msg (Printf.sprintf "%s[Error]%s %s" Terminal.red Terminal.reset e)
       )
      errors;
    if flags <> [] then msg "Flagged";

    let observable_ok =
      List.for_all
        (fun (cond, mem_cond) ->
           let matched =
             List.exists
               (fun fs -> check_outcome fs cond && check_mem_outcome fs mem_cond)
               final_states
           in
           if (not matched) && final_states <> [] then
             msg
               (Printf.sprintf "%sObservable not found%s: %s %s" Terminal.red
                  Terminal.reset (cond_to_string cond)
                  (mem_cond_to_string mem_cond)
               );
           matched
         )
        observable
    in

    let unobservable_ok =
      List.for_all Fun.id
        (List.mapi
           (fun i fs ->
              match
                List.find_opt
                  (fun (cond, mem_cond) ->
                     check_outcome fs cond && check_mem_outcome fs mem_cond
                   )
                  unobservable
              with
              | Some (cond, mem_cond) ->
                  msg
                    (Printf.sprintf
                       "%sUnobservable found%s in execution %d: %s %s"
                       Terminal.red Terminal.reset (i + 1) (cond_to_string cond)
                       (mem_cond_to_string mem_cond)
                    );
                  false
              | None -> true
            )
           final_states
        )
    in

    let result =
      if results = [] then NoBehaviour
      else if errors <> [] then ModelError
      else if observable_ok && unobservable_ok then Expected
      else Unexpected
    in
    (result, List.rev !msgs)

  let run_testrepr print_final_states model (test : Testrepr.t) =
    let fuel = Config.get_fuel () in
    let (init, term) = AS.testrepr_to_archstate test in
    run_executions print_final_states model init fuel term test

  let run_litmus_test ~parse print_final_states model filename =
    let name = Filename.basename filename in
    if not (Sys.file_exists filename) then (
      Printf.printf "  %s✗%s %s  %sfile not found%s\n" Terminal.red Terminal.reset
        name Terminal.red Terminal.reset;
      ParseError
    )
    else
      try
        let test = parse filename in
        let (result, msgs) = run_testrepr print_final_states model test in
        let (icon, color) =
          match result with
          | Expected -> (Terminal.check, Terminal.green)
          | Unexpected -> (Terminal.cross, Terminal.yellow)
          | _ -> (Terminal.cross, Terminal.red)
        in
        Printf.printf "\n%s%s%s %s\n" color icon Terminal.reset name;
        Printf.printf "Test %s Allowed\n" test.name;
        List.iter (fun m -> Printf.printf "%s\n" m) msgs;
        result
      with Otoml.Parse_error (pos, msg) ->
        Printf.printf "%s✗%s %s  %sparse error at %s: %s%s\n" Terminal.red
          Terminal.reset name Terminal.red
          (Option.fold ~none:"?"
             ~some:(fun (l, c) -> Printf.sprintf "%d:%d" l c)
             pos
          )
          msg Terminal.reset;
        ParseError
end
