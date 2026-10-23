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

module Assertion = Litmus.Assertion

(** {1 Isla test internal representation } *)
module Arch_id = Litmus.Arch_id

module Toml = Litmus.Toml

type thread =
  { tid : int;
    code : string;
    regs : (string * Term.t) list;
    breakpoints : Term.t list
  }

type section =
  { sec_name : string;
    address : int option;
    code : string
  }

type t =
  { arch : Arch_id.t;
    name : string;
    threads : thread list;
    sections : section list;
    page_table_setup : Page_table_ast.stmt list;
    symbolic : string list;
    sizes : (string * int) list;
    (* [name, (base, offset)]: [name] is defined as [base + offset] instead of
       being allocated. *)
    offsets : (string * (string * int)) list;
    locations : (string * Term.t) list;
    kind : Litmus.Testrepr.kind;
    assertion : Term.t Assertion.expr
  }

(** {1 Isla test parsing } *)

module I = Parser.MenhirInterpreter
module E = MenhirLib.ErrorReports

(** Show the fragment of [text] between two positions, shortened to fit in an
    error message *)
let show_text text positions =
  E.extract text positions |> E.sanitize |> E.compress |> E.shorten 20

(** Run the incremental parser [entry] on [lexbuf], which reads [text]. On a
    syntax error, return the message of the error state from [parser.messages],
    in which every [$i] is replaced by the text of the [i]-th element of the
    parser stack, counting from the top starting at 0 (as in the Menhir
    calc-syntax-errors demo) *)
let run_parser entry text lexbuf =
  let supplier = I.lexer_lexbuf_to_supplier Lexer.token lexbuf in
  let fail = function
    | I.HandlingError env ->
        let get i =
          match I.get i env with
          | Some (I.Element (_, _, pos1, pos2)) -> show_text text (pos1, pos2)
          | None -> "???"
        in
        let msg =
          try Parser_messages.message (I.current_state_number env)
          with Not_found -> "Syntax error."
        in
        Error (E.expand get msg |> String.trim)
    | _ -> assert false
  in
  I.loop_handle Result.ok fail supplier (entry lexbuf.lex_curr_p)

(** Describe the token on which a syntax error happened *)
let unexpected_token lexbuf =
  match Lexing.lexeme lexbuf with
  | "" -> "unexpected end of input"
  | tok -> Printf.sprintf "unexpected '%s'" tok

let parse_term : Toml.t -> Term.t = function
  | TomlInteger i -> Term.Const i
  | TomlString s -> (
      let lexbuf = Lexing.from_string s in
      match run_parser Parser.Incremental.binding s lexbuf with
      | Ok v -> v
      | Error msg ->
          Toml.error "term parse error at position %d (%s) in: %s\n%s"
            lexbuf.lex_curr_p.pos_cnum (unexpected_token lexbuf) s msg
      | exception Lexer.Error msg -> Toml.error "%s" msg
    )
  | value ->
      Toml.error
        "Isla value is invalid, should be int or string expression, but is: %s"
        (Toml.Printer.to_string value)

let is_meta_key k = String.starts_with ~prefix:"__isla" k

let parse_reset_entry k v =
  if is_meta_key k then None
  else
    let value =
      try parse_term v
      with Toml.Path_error (path, Toml.GenError msg) ->
        Toml.error ~path "register %s has invalid reset value: %s" k msg
    in
    Some (k, value)

let parse_reset_table toml =
  Toml.get_table_key_values parse_reset_entry toml |> List.filter_map Fun.id

let parse_thread tid table =
  let tid = Litmus.Parser.parse_tid tid in
  let code = Toml.find table Toml.get_string ["code"] |> String.trim in
  let init =
    Toml.find_or ~default:[] table (Toml.get_table_values parse_term) ["init"]
  in
  let reset = Toml.find_or ~default:[] table parse_reset_table ["reset"] in
  List.iter
    (fun (k, _) ->
       if List.mem_assoc k init then
         Toml.error "register %s is defined in both init and reset" k
     )
    reset;
  let regs = init @ reset in
  let breakpoints =
    Toml.find_or ~default:[] table (Toml.get_array parse_term) ["breakpoints"]
  in
  {tid; code; regs; breakpoints}

let parse_threads toml =
  let l =
    Toml.get_table_key_values parse_thread toml
    |> List.sort (fun a b -> compare a.tid b.tid)
  in
  List.iteri (fun i t -> if i != t.tid then Toml.error "Thread %i is missing" i) l;
  l

let parse_section name table =
  let address =
    Toml.find_opt table (Toml.get_integer ~strict:false) ["address"]
  in
  let code = Toml.find table Toml.get_string ["code"] |> String.trim in
  {sec_name = name; address; code}

let parse_sections toml = Toml.get_table_key_values parse_section toml

let parse_assertion_expr s =
  let lexbuf = Lexing.from_string s in
  match run_parser Parser.Incremental.assertion s lexbuf with
  | Ok e -> e
  | Error msg ->
      Toml.error "assertion parse error at position %d (%s) in: %s\n%s"
        lexbuf.lex_curr_p.pos_cnum (unexpected_token lexbuf) s msg
  | exception Lexer.Error msg -> Toml.error "%s" msg

let parse_assertion toml =
  let assertion_str = Toml.get_string toml |> String.trim in
  if assertion_str = "" then Assertion.True
  else parse_assertion_expr assertion_str |> Assertion.flatten

let parse_arch toml =
  let arch_string = Toml.get_string toml in
  try Litmus.Arch_id.of_string arch_string
  with Litmus.Arch_id.UnknownArch arch ->
    Toml.error "Unknown architecture \"%s\"" arch

let parse_sizes toml = Toml.get_table_values Toml.get_positive toml

let parse_offset toml =
  let offset = Toml.find toml Toml.get_integer ["offset"] in
  if offset < 0 then
    Toml.error ~path:["offset"] "Expected non-negative integer, got %i" offset;
  (Toml.find toml Toml.get_string ["base"], offset)

let parse_offsets toml = Toml.get_table_values parse_offset toml

let lexbuf_line_char lexbuf =
  let pos = Lexing.lexeme_start_p lexbuf in
  (pos.pos_lnum, pos.pos_cnum - pos.pos_bol + 1)

let parse_page_table_setup toml =
  let s = Toml.get_string toml |> String.trim in
  let lexbuf = Lexing.from_string s in
  match run_parser Parser.Incremental.page_table_setup s lexbuf with
  | Ok stmts -> stmts
  | Error msg ->
      let (line, character) = lexbuf_line_char lexbuf in
      Toml.error "page-table setup parse error at line %d, character %d (%s):\n%s"
        line character (unexpected_token lexbuf) msg
  | exception Failure msg -> Toml.error "page-table setup parse error: %s" msg
  | exception Lexer.Error msg -> Toml.error "%s" msg

let of_toml toml =
  { arch = Toml.find toml parse_arch ["arch"];
    name = Toml.find_or ~default:"unknown" toml Toml.get_string ["name"];
    threads = Toml.find toml parse_threads ["thread"];
    sections = Toml.find_or ~default:[] toml parse_sections ["section"];
    page_table_setup =
      Toml.find_or ~default:[] toml parse_page_table_setup ["page_table_setup"];
    symbolic =
      Toml.find_or ~default:[] toml (Toml.get_array Toml.get_string) ["symbolic"];
    sizes = Toml.find_or ~default:[] toml parse_sizes ["sizes"];
    offsets = Toml.find_or ~default:[] toml parse_offsets ["offsets"];
    locations =
      Toml.find_or ~default:[] toml
        (Toml.get_table_values parse_term)
        ["locations"];
    kind = Litmus.Parser.parse_kind toml;
    (* We voluntarily ignore the [expect] field *)
    assertion =
      Toml.find_or ~default:Assertion.True toml parse_assertion
        ["final"; "assertion"]
  }
