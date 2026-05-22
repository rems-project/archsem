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

(** This module is here to help error handling *)

(** Raise a fatal error with [code], adds "archsem: error" in front*)
let fatal ?(code = 1) fmt =
  Printf.eprintf "archsem: %s%sfatal error:%s " Terminal.red Terminal.bold
    Terminal.reset;
  Printf.kfprintf (fun _ -> Printf.eprintf "\n"; exit code) stderr fmt

let assert_fatal ?(code = 1) (cond : bool) fmt =
  if cond then Printf.ikfprintf (fun _ -> ()) stderr fmt else fatal ~code fmt

let parse_error file loc fmt =
  Printf.eprintf "archsem: %s%sparse error:%s\n" Terminal.red Terminal.bold
    Terminal.reset;
  ( match loc with
  | Some (line, col) ->
      Printf.eprintf "%sFile %s, line %d, character %d:%s\n" Terminal.bold file
        line col Terminal.reset
  | None -> Printf.eprintf "%sFile %s:%s\n" Terminal.bold file Terminal.reset
  );
  Printf.kfprintf (fun fmt -> Printf.fprintf fmt "\n") stderr fmt

let toml_error file path fmt =
  Printf.eprintf "archsem: %s%sTOML error:%s\n" Terminal.red Terminal.bold
    Terminal.reset;
  if path == [] then
    Printf.eprintf "%sFile \"%s\":%s\n" Terminal.bold file Terminal.reset
  else
    Printf.eprintf "%sFile \"%s\", path \"%s\":%s\n" Terminal.bold file
      (String.concat "." path) Terminal.reset;
  Printf.kfprintf (fun fmt -> Printf.fprintf fmt "\n") stderr fmt

let model_error test msg =
  Printf.eprintf "archsem: %s%smodel error:%s\n" Terminal.red Terminal.bold
    Terminal.reset;
  Printf.eprintf "%sTest \"%s\":%s\n%s\n" Terminal.bold test Terminal.reset msg
