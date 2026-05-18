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

(** Run a litmus test and display results *)

module Make (Arch : Archsem.Arch) = struct
  open Arch
  module AS = ToArchState.Make (Arch)
  module AssertionChecker = Assertion.Checker (Arch)

  (** Run a test in a given model, print [short] or long output.
      raises [Exit] if something went wrong, after printing message on [stderr] *)
  let run_testrepr ~short model (test : Testrepr.t) =
    let fuel = Config.get_fuel () in
    let (init, term) = AS.testrepr_to_archstate test in
    let time_start = Sys.time () in
    let results = model fuel term init in
    let time_end = Sys.time () in
    let time = time_end -. time_start in
    let errors =
      List.filter_map
        (function ArchModel.Res.Error e -> Some e | _ -> None)
        results
    in
    if errors != [] then (
      List.iter (Error.model_error test.name) errors;
      raise Exit
    );

    let flags =
      List.filter_map
        (function ArchModel.Res.Flagged x -> Some x | _ -> None)
        results
    in
    if flags != [] then (
      Error.model_error test.name "Flags unsupported";
      raise Exit
    );

    let final_states =
      List.filter_map
        (function ArchModel.Res.FinalState fs -> Some fs | _ -> None)
        results
    in
    if final_states == [] then (
      Error.model_error test.name "No behaviour";
      raise Exit
    );

    let resolve_sym sym =
      let block = Testrepr.mem_by_sym sym test.memory in
      (block.addr, Testrepr.block_size block)
    in

    let (observed, not_observed) =
      List.partition
        (fun fs -> AssertionChecker.check_assertion ~resolve_sym fs test.final)
        final_states
    in

    let obs_count = List.length observed in
    let not_obs_count = List.length not_observed in

    if short then Mcompare.print_observation test.name obs_count not_obs_count
    else
      let locations = Assertion.get_unique_locs test.final in
      let min_states =
        List.map
          (fun fs ->
             List.map
               (fun loc -> (loc, AssertionChecker.lookup_loc ~resolve_sym fs loc))
               locations
           )
          final_states
      in
      let min_states = List.sort_uniq compare min_states in
      Mcompare.print test min_states obs_count not_obs_count time

  (** Run a testfile in a given model.
      @param parse is the parsing function (filename to Testrepr.t)
                   This parsing function may do isla conversion
      @param short requires either short form output (observation line) or
                   full output.
      Raises [Exit] on test error, the error was already printed on [stderr] *)
  let run_test_file ~parse ~short model filename =
    let name = Filename.basename filename in
    if not (Sys.file_exists filename) then Error.fatal "file not found: %s" name;
    let test =
      try parse filename with
      | Toml.Parse_error (pos, msg) ->
          Error.parse_error filename pos "%s" msg;
          raise Exit
      | Toml.Path_error (path, FieldMissing field) ->
          Error.toml_error filename path "Missing field: %s" field;
          raise Exit
      | Toml.Path_error (path, GenError msg) ->
          Error.toml_error filename path "%s" msg;
          raise Exit
    in
    run_testrepr ~short model test
end
