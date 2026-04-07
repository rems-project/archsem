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

type thread =
  { tid : int;
    code : string;
    init : (string * Term.t) list
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
  { arch : Litmus.Arch_id.t;
    name : string;
    threads : thread list;
    sections : section list;
    symbolic : string list;
    locations : (string * Term.t) list;
    expect : expect;
    assertion : Assertion.expr
  }

(** {1 Isla test parsing } *)

let type_error fmt = Printf.ksprintf (fun s -> raise (Otoml.Type_error s)) fmt

let is_label s =
  let n = String.length s in
  n >= 2
  && s.[n - 1] = ':'
  &&
  let body = String.sub s 0 (n - 1) in
  String.for_all
    (fun c ->
       c = '_'
       || (c >= 'A' && c <= 'Z')
       || (c >= 'a' && c <= 'z')
       || (c >= '0' && c <= '9')
     )
    body

let parse_value = function
  | Otoml.TomlInteger i -> Term.Const (Z.of_int i)
  | Otoml.TomlString s -> (
    try Term.Const (Z.of_string s)
    with Invalid_argument _ ->
      if is_label s then Term.LocVal (Label (String.sub s 0 (String.length s - 1)))
      else Term.LocVal (Term.Mem s)
  )
  | value ->
      type_error "Value is invalid, should be int or string, but is: %s"
        (Otoml.Printer.to_string value)

let is_meta_key k = String.starts_with ~prefix:"__isla" k

let parse_thread (tid, table) =
  let tid =
    match int_of_string_opt tid with
    | Some tid -> tid
    | None -> type_error "Thread table contained a non-number field: %s" tid
  in
  let _ = Otoml.get_table table in
  let code = Otoml.find table Otoml.get_string ["code"] |> String.trim in
  let init =
    Otoml.find_or ~default:[] table (Otoml.get_table_values parse_value) ["init"]
  in
  let reset =
    Otoml.find_or ~default:[] table Otoml.get_table ["reset"]
    |> List.filter (fun (k, _) -> not (is_meta_key k))
    |> List.map (fun (k, v) -> (k, parse_value v))
  in
  let init_keys = List.map fst init in
  let merged =
    init @ List.filter (fun (k, _) -> not (List.mem k init_keys)) reset
  in
  {tid; code; init = merged}

let parse_threads toml =
  let table = Otoml.get_table toml in
  List.sort (fun a b -> compare a.tid b.tid) (List.map parse_thread table)

let parse_address = function
  | Otoml.TomlInteger i -> i
  | Otoml.TomlString s -> (
    try Z.to_int (Z.of_string s)
    with Invalid_argument _ | Z.Overflow ->
      raise (Otoml.Type_error ("invalid address: " ^ s))
  )
  | v ->
      raise
        (Otoml.Type_error
           ("address must be integer or hex string, got: "
          ^ Otoml.Printer.to_string v
           )
        )

let parse_section (name, table) =
  let _ = Otoml.get_table table in
  let address = Otoml.find table parse_address ["address"] in
  let code = Otoml.find table Otoml.get_string ["code"] |> String.trim in
  {sec_name = name; address; code}

let parse_sections toml =
  let table = Otoml.get_table toml in
  List.map parse_section table

let parse_expect toml =
  match Otoml.get_string toml with
  | "sat" -> Sat
  | "unsat" -> Unsat
  | expect -> raise (Otoml.Type_error ("invalid expectation value: " ^ expect))

let parse_assertion_expr s =
  let lexbuf = Lexing.from_string s in
  try Parser.assertion Lexer.token lexbuf
  with Parser.Error ->
    type_error "assertion parse error at position %d in: %s"
      lexbuf.lex_curr_p.pos_cnum s

let parse_assertion toml =
  let assertion_str = Otoml.get_string toml |> String.trim in
  if assertion_str = "" then Assertion.True
  else parse_assertion_expr assertion_str

let parse_arch toml =
  let arch_string = Otoml.get_string toml in
  try Litmus.Arch_id.of_string arch_string
  with Failure msg -> raise (Otoml.Type_error msg)

let of_toml toml =
  { arch = Otoml.find toml parse_arch ["arch"];
    name = Otoml.find_or ~default:"unknown" toml Otoml.get_string ["name"];
    threads = Otoml.find toml parse_threads ["thread"];
    sections = Otoml.find_or ~default:[] toml parse_sections ["section"];
    symbolic =
      Otoml.find_or ~default:[] toml
        (Otoml.get_array Otoml.get_string)
        ["symbolic"];
    locations =
      Otoml.find_or ~default:[] toml
        (Otoml.get_table_values parse_value)
        ["locations"];
    expect = Otoml.find_or ~default:Sat toml parse_expect ["final"; "expect"];
    assertion =
      Otoml.find_or ~default:Assertion.True toml parse_assertion
        ["final"; "assertion"]
  }
