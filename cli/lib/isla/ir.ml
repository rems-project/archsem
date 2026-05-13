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

(** Parse isla-format TOML into an intermediate representation. *)

(** {1 Isla test internal representation } *)
module Arch_id = Litmus.Arch_id

module Toml = Litmus.Toml

type value =
  | Int of Z.t
  | Sym of string

type thread =
  { tid : int;
    code : string;
    init : (string * value) list
  }

type section =
  { sec_name : string;
    address : int;
    code : string
  }

type expect =
  | Sat
  | Unsat

type t =
  { arch : Arch_id.t;
    name : string;
    threads : thread list;
    sections : section list;
    symbolic : string list;
    locations : (string * value) list;
    expect : expect;
    assertion : Assertion.expr
  }

(** {1 Isla test parsing } *)

let parse_value : Toml.t -> value = function
  | TomlInteger i -> Int i
  | TomlString s -> (
    try Int (Z.of_string s) with Invalid_argument _ -> Sym s
  )
  | value ->
      Toml.error "Isla value is invalid, should be int or string, but is: %s"
        (Toml.Printer.to_string value)

let parse_thread (tid, table) =
  let tid =
    match int_of_string_opt tid with
    | Some tid ->
        if tid < 0 then Toml.error "Thread number can't be negative: %i" tid;
        tid
    | None -> Toml.error "Thread table contained a non-number field: %s" tid
  in
  let code = Toml.find table Toml.get_string ["code"] |> String.trim in
  let init =
    Toml.find_or ~default:[] table (Toml.get_table_values parse_value) ["init"]
  in
  {tid; code; init}

let parse_threads toml =
  let table = Toml.get_table toml in
  let l =
    List.sort (fun a b -> compare a.tid b.tid) (List.map parse_thread table)
  in
  List.iteri (fun i t -> if i != t.tid then Toml.error "Thread %i is missing" i) l;
  l

let parse_section name table =
  let address = Toml.find table Toml.get_integer ["address"] in
  let code = Toml.find table Toml.get_string ["code"] |> String.trim in
  {sec_name = name; address; code}

let parse_sections toml = Toml.get_table_key_values parse_section toml

let parse_expect toml =
  match Toml.get_string toml with
  | "sat" -> Sat
  | "unsat" -> Unsat
  | expect ->
      Toml.error "Expected expectation value (\"sat\" or \"unsat\"), found: %s"
        expect

let parse_assertion_expr s =
  let lexbuf = Lexing.from_string s in
  try Parser.assertion Lexer.token lexbuf
  with Parser.Error ->
    Toml.error "assertion parse error at position %d in: %s"
      lexbuf.lex_curr_p.pos_cnum s

let parse_assertion toml =
  let assertion_str = Toml.get_string toml |> String.trim in
  if assertion_str = "" then Assertion.True
  else parse_assertion_expr assertion_str

let parse_arch toml =
  let arch_string = Toml.get_string toml in
  try Litmus.Arch_id.of_string arch_string
  with Litmus.Arch_id.UnknownArch arch ->
    Toml.error "Unknown architecture \"%s\"" arch

let of_toml toml =
  { arch = Toml.find toml parse_arch ["arch"];
    name = Toml.find_or ~default:"unknown" toml Toml.get_string ["name"];
    threads = Toml.find toml parse_threads ["thread"];
    sections = Toml.find_or ~default:[] toml parse_sections ["section"];
    symbolic =
      Toml.find_or ~default:[] toml (Toml.get_array Toml.get_string) ["symbolic"];
    locations =
      Toml.find_or ~default:[] toml
        (Toml.get_table_values parse_value)
        ["locations"];
    expect = Toml.find_or ~default:Sat toml parse_expect ["final"; "expect"];
    assertion =
      Toml.find_or ~default:Assertion.True toml parse_assertion
        ["final"; "assertion"]
  }
