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

(** This file actually runs in the converter directory (parent) but the
    generated rules run in the expect directory*)

(** Expects [arm/um/test.*.toml]*)
let generate_rules file =
  (* Dune doesn't support generating files in subdirectory, or importing
     subdirectory stanza with dynamic_include so we have to flatten the
     directory structure*)
  let flat = file |> String.split_on_char '/' |> String.concat "_" in
  Printf.printf
    {|
(rule
 (deps (:input ../../%s) (source_tree ../../../../config))
 (targets %s)
 (action
  (run archsem convert %%{input} -o %%{targets})))

(rule
 (alias runtest)
 (action
  (diff %s %s)))
|}
     file flat file flat

let gen_for_dir dir =
  if Sys.is_directory (Filename.concat ".." dir) then
    Sys.readdir (Filename.concat "../" dir)
    |> Array.to_list |> List.sort String.compare
    |> List.map (fun s -> Filename.concat dir s)
    |> List.filter (fun s -> Filename.check_suffix s ".toml")
    |> List.iter generate_rules

let gen_for_arch arch =
  Sys.readdir ("../" ^ arch)
  |> Array.to_list |> List.sort String.compare
  |> List.map (fun s -> Filename.concat arch s)
  |> List.iter gen_for_dir

let () = gen_for_arch "arm"; gen_for_arch "x86"
