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

(** Terminal formatting: ANSI color codes, Unicode symbols, and display helpers. *)

let reset = "\027[0m"

let bold = "\027[1m"

let dim = "\027[2m"

let red = "\027[31m"

let green = "\027[32m"

let yellow = "\027[33m"

let cyan = "\027[36m"

(** Unicode symbols *)
let check = "✓"

let cross = "✗"

let dot = "·"

(** {1 Display helpers} *)

let separator () =
  Printf.printf "%s──────────────────────────────────────────%s\n" dim reset

let print_header model_name count =
  Printf.printf "\n%s%s%s%s  %d tests\n\n" bold cyan model_name reset count

let print_summary ~model_name ~total ~failures =
  assert (total > 1);
  let all_pass = failures == 0 in
  let status_color = if all_pass then green else red in
  let repeat n s = String.concat "" (List.init n (fun _ -> s)) in
  let success = total - failures in

  Printf.printf "\n";
  separator ();

  Printf.printf "  %s%sSUMMARY%s  %s %s %d tests\n" bold status_color reset
    model_name dot total;

  let bar_w = 42 in
  let filled = success * bar_w / total in
  let empty = bar_w - filled in
  let pct = success * 100 / total in
  Printf.printf "  %s%s%s%s%s %d%%%s\n" status_color (repeat filled "█") dim
    (repeat empty "░") status_color pct reset;

  separator ();
  Printf.printf "\n"
