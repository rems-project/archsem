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

(** Litmus test TOML parser.

    Parses TOML files describing litmus tests:
    - [[registers]]: Initial register state per thread
    - [[memory]]: Initial memory contents
    - [[termCond]]: Termination conditions per thread (typically PC values)
    - [[final]]: Final condition
      - [[kind]]: Test kind (exists/forall/notexists)
      - [[assertion]]: The assertion in funky TOML syntax

    Parsing path: TOML -> Testrepr.t *)

module RegValGen = Archsem.RegValGen

(** {1 TOML -> Testrepr.t} *)

(** Convert a TOML value to RegValGen.t *)
let rec toml_to_gen : Toml.t -> RegValGen.t = function
  | TomlInteger i -> Number i
  | TomlString s -> String s
  | TomlArray l -> Array (List.map toml_to_gen l)
  | TomlTable t | TomlInlineTable t ->
      Struct (List.map (fun (k, v) -> (k, toml_to_gen v)) t)
  | v -> Toml.error "Unsupported register value type: %s" (Toml.toml_type_name v)

(** Parse [[registers]] into register lists with string keys *)
let parse_test_registers toml =
  let parse_regs = Toml.get_table_values toml_to_gen in
  Toml.find toml (Toml.get_array parse_regs) ["registers"]

(** Parse a memory block in [[memory]] *)

(** Parse [[memory]] into abstract memory blocks *)
let parse_test_memory toml : Testrepr.memory_block list =
  let parse_memory_block (table : Toml.t) : Testrepr.memory_block =
    let addr = Toml.find table Toml.get_integer ["addr"] in
    let step = Toml.find table Toml.get_integer ["step"] in
    if step <= 0 then
      Toml.error ~path:["step"] "Memory block step must be positive";
    let get_sized_Z step toml =
      let z = Toml.get_Z toml in
      if Z.sign z < 0 then
        Toml.error "Negative memory data is not allowed: %s" (Z.format "%#x" z);
      if Z.numbits z > 8 * step then
        Toml.error "Memory data number (%s) contains %d bytes but the step is %d"
          (Z.format "%#x" z)
          ((Z.numbits z + 7) / 8)
          step;
      z
    in
    let values =
      Toml.find table (Toml.get_array ~strict:false (get_sized_Z step)) ["data"]
    in
    let n = List.length values in
    let data = Bytes.make (n * step) (Char.chr 0) in
    List.iteri
      (fun i v ->
         let vbytes = Z.to_bits v in
         Bytes.blit_string vbytes 0 data (i * step)
           (min step (String.length vbytes))
       )
      values;
    let sym = Toml.find_opt table Toml.get_string ["sym"] in
    let get_memory_kind toml : Testrepr.memory_kind =
      match Toml.get_string toml with
      | "data" -> Data
      | "code" -> Code
      | "pagetable" -> PageTable
      | s ->
          Toml.error
            "Expect memory kind (\"data\", \"code\", \"pagetable\") but got: %s" s
    in
    let kind =
      Toml.find_or ~default:Testrepr.Data table get_memory_kind ["kind"]
    in
    ( if kind = Code then
        match sym with
        | Some s -> Toml.error "memory code blocks must not have sym but got %s" s
        | None -> ()
    );
    {addr; step; data; sym; kind}
  in
  Toml.find toml (Toml.get_array parse_memory_block) ["memory"]

(** Parse [[termCond]] into term cond lists with string keys *)
let parse_test_termcond toml : (string * RegValGen.t) list list =
  Toml.find toml (Toml.get_array (Toml.get_table_values toml_to_gen)) ["termCond"]

(** {2 Final condition parsing} *)

(** Parse a location string, either ["0:R0"] or ["x"] *)
let parse_location_string str : Assertion.loc =
  match String.split_on_char ':' str with
  | [thread; reg] ->
      let thread =
        try int_of_string thread
        with Failure msg ->
          Toml.error
            "Thread number in final assertion on register is not a number: %s" msg
      in
      Assertion.Reg (thread, reg)
  | [mem] ->
      if String.length mem == 0 then
        Toml.error "Assertion location can't be empty";
      (* This case catches the "0.R0" instead of "0:R0" mistake *)
      let is_digit chr = chr >= '0' && chr <= '9' in
      if is_digit mem.[0] then
        Toml.error "Assertion location \"%s\" starts with a digit" mem;
      Assertion.Mem mem
  | _ -> Toml.error "Assertion location has more than one ':'"

let parse_atom key toml : Z.t Assertion.atom =
  let lhs = parse_location_string key in
  match toml with
  | Toml.TomlString s -> Assertion.CmpLoc (lhs, parse_location_string s)
  | TomlInteger z -> Assertion.CmpCst (lhs, z)
  | _ -> Toml.error "right hand side must be location or integer"

(* This TOML encoding is very simple, but will fail if a memory location is
   called "and, or, not" or contains colons *)
let rec parse_assertion : Toml.t -> Z.t Assertion.expr = function
  | TomlBoolean true -> Assertion.True
  | TomlBoolean false -> Assertion.False
  | toml ->
      let parse_singleton key toml =
        match key with
        | "and" -> Assertion.And (Toml.get_array parse_assertion toml)
        | "or" -> Assertion.Or (Toml.get_array parse_assertion toml)
        | "not" -> Assertion.Not (parse_assertion toml)
        | k -> Assertion.Atom (parse_atom k toml)
      in
      Toml.get_singleton parse_singleton toml

(** {2 Parse test kinds} *)

let parse_kind toml : Testrepr.kind =
  let parse_kind_string toml : Testrepr.kind =
    match Toml.get_string toml with
    | "exists" -> Exists
    | "forall" -> Forall
    | "notexists" -> NotExists
    | s ->
        Toml.error
          "Expected test kind (\"exists\", \"forall\", \"notexists\"), got %s" s
  in
  Toml.find_or ~default:Testrepr.Exists toml parse_kind_string ["final"; "kind"]

(** {2 Top-level parser} *)

let parse_to_testrepr : Toml.t -> Testrepr.t =
 fun toml ->
  { Testrepr.arch = Toml.find toml Toml.get_string ["arch"];
    name = Toml.find toml Toml.get_string ["name"];
    registers = parse_test_registers toml;
    memory = parse_test_memory toml;
    term_cond = parse_test_termcond toml;
    final =
      Toml.find_or ~default:Assertion.True toml parse_assertion
        ["final"; "assertion"];
    kind = parse_kind toml
  }
