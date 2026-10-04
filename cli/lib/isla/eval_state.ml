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

(** Mutable evaluation state owned by one test. *)

type page_table = (int, int64) Hashtbl.t

type t =
  { symbols : (string, int) Hashtbl.t;
    mutable page_table : page_table option
  }

let create () = {symbols = Hashtbl.create 32; page_table = None}

(** Decides if a string is an Archsem symbol: must start with a ASCII letter or
    [_] and followed by alphanumeric character (or [_]).
    Ideally this should match the `ident` non terminal in the lexer *)
let is_valid_symbol_name name =
  let is_ident_start = function
    | 'a' .. 'z' | 'A' .. 'Z' | '_' -> true
    | _ -> false
  in
  let is_ident_char = function '0' .. '9' -> true | c -> is_ident_start c in
  name <> "" && is_ident_start name.[0] && String.for_all is_ident_char name

(** Check if a string is a valid symbol name *)
let check_symbol_name name =
  if not (is_valid_symbol_name name) then
    Printf.ksprintf failwith
      "Symbol %S is invalid: names must start with a letter or '_' and only \
       contain letters, digits and '_'"
       name

let check_fresh_symbol state name =
  check_symbol_name name;
  if Hashtbl.mem state.symbols name then
    Printf.ksprintf failwith "Symbol %s is already defined" name

let add_symbol state name addr =
  check_fresh_symbol state name;
  Hashtbl.add state.symbols name addr

let lookup_addr state name =
  match Hashtbl.find_opt state.symbols name with
  | Some addr -> addr
  | None -> Printf.ksprintf failwith "Symbol %s not found" name
