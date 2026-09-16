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

(** This file actually runs in the logs directory (parent) but the generated
    rules run in the expect directory.

    For each test and each model that should run it, generate a rule that runs
    the model on the test and diffs the resulting log (minus the [Time] line)
    against the expected log in [expect/<arch>/<dir>/<test>.<model>.log] *)

(** Models to run on each test directory *)
let models_for_dir arch dir =
  match (arch, dir) with
  | ("arm", ("seq" | "seq-mixed")) -> ["seq"; "ump"; "vmp"]
  | ("arm", ("um" | "um-mixed")) -> ["ump"; "vmp"]
  | ("arm", ("vm" | "vm-mixed")) -> ["vmp"]
  | ("x86", "seq") -> ["seq"; "tso"]
  | ("x86", "um") -> ["tso"]
  | _ ->
      Printf.eprintf "gen: unknown test directory %s/%s, add it to %s\n" arch dir
        __FILE__;
      exit 1

(** Expects [arm/um/test.*.toml] *)
let generate_rules model file =
  let log = Filename.remove_extension file ^ "." ^ model ^ ".log" in
  (* Dune doesn't support generating files in subdirectory, or importing
     subdirectory stanza with dynamic_include so we have to flatten the
     directory structure*)
  let flat = log |> String.split_on_char '/' |> String.concat "_" in
  Printf.printf
    {|
(rule
 (deps (:input ../../%s) (source_tree ../../../../config))
 (targets %s)
 (action
  (with-stdout-to %%{targets}
   (pipe-stdout
    (run archsem %s %%{input})
    (run sed "/^Time /d"))))) ; Remove the time line, it would make the test flaky

(rule
 (alias runtest)
 (action
  (diff %s %s)))
|}
    file flat model log flat

let gen_for_dir arch dir =
  let path = Filename.concat arch dir in
  (* Skip hidden directories and '.'/'..' *)
  if dir.[0] <> '.' && Sys.is_directory (Filename.concat ".." path) then
    let models = models_for_dir arch dir in
    Sys.readdir (Filename.concat ".." path)
    |> Array.to_list |> List.sort String.compare
    |> List.filter (fun s -> Filename.check_suffix s ".toml")
    |> List.map (Filename.concat path)
    |> List.iter (fun file -> List.iter (fun m -> generate_rules m file) models)

let gen_for_arch arch =
  Sys.readdir (Filename.concat ".." arch)
  |> Array.to_list |> List.sort String.compare
  |> List.iter (gen_for_dir arch)

let () = gen_for_arch "arm"; gen_for_arch "x86"
