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

(** Litmus test TOML printer.

    Converts Testrepr.t to TOML via Toml. *)

(** {1 Value Conversion} *)

let rec gen_to_toml (v : Archsem.RegValGen.t) : Toml.t =
  match v with
  | Number z -> TomlInteger z
  | String s -> TomlString s
  | Array vs -> TomlArray (List.map gen_to_toml vs)
  | Struct fields ->
      TomlInlineTable (List.map (fun (k, field) -> (k, gen_to_toml field)) fields)

let req_to_toml (req : Testrepr.reg_requirement) : Toml.t =
  match req with
  | ReqEq v -> gen_to_toml v
  | ReqNe v -> TomlInlineTable [("op", TomlString "ne"); ("val", gen_to_toml v)]

(** {1 Threads} *)

let registers_to_toml regs : Toml.t =
  TomlTable (List.map (fun (reg, rv) -> (reg, gen_to_toml rv)) regs)

let breakpoints_to_toml breakpoints : Toml.t =
  TomlArray (List.map Toml.integer breakpoints)

let thread_to_toml (thread : Testrepr.thread) : Toml.t =
  TomlTable
    [ ("regs", registers_to_toml thread.regs);
      ("breakpoints", breakpoints_to_toml thread.breakpoints)
    ]

let threads_to_toml (threads : Testrepr.thread list) : Toml.t =
  TomlTable
    (List.mapi
       (fun tid thread -> (string_of_int tid, thread_to_toml thread))
       threads
    )

(** {1 Memory} *)

let memory_block_to_toml (block : Testrepr.memory_block) : Toml.t =
  let step = block.step in
  assert (step > 0);
  let len = Bytes.length block.data in
  let n = len / step in
  assert (len = n * step);
  let values =
    List.init n (fun i -> Bytes.sub_string block.data (i * step) step |> Z.of_bits)
  in
  let data_toml : Toml.t =
    match values with
    | [single] -> Toml.TomlInteger single
    | multiple -> Toml.TomlArray (List.map (fun v -> Toml.TomlInteger v) multiple)
  in
  TomlTable
    (( match block.sym with
       | Some sym -> [("sym", Toml.TomlString sym)]
       | None -> []
       )
    @ ( match block.kind with
      | Testrepr.Data -> []
      | kind -> [("kind", Toml.TomlString (Testrepr.string_of_memory_kind kind))]
      )
    @ [ ("addr", Toml.TomlInteger (Z.of_int block.addr));
        ("step", Toml.TomlInteger (Z.of_int step));
        ("data", data_toml)
      ]
    )

(** {1 Final condition} *)

let location_to_string : Assertion.loc -> string = function
  | Reg (thread, reg) -> Printf.sprintf "%d:%s" thread reg
  | Mem mem -> mem

let atom_to_toml : Z.t Assertion.atom -> Toml.t = function
  | CmpCst (loc, cst) ->
      TomlInlineTable [(location_to_string loc, TomlInteger cst)]
  | CmpLoc (loc, loc') ->
      TomlInlineTable
        [(location_to_string loc, TomlString (location_to_string loc'))]

let rec assertion_to_toml : Z.t Assertion.expr -> Toml.t = function
  | Atom atom -> atom_to_toml atom
  | And exprs ->
      TomlInlineTable [("and", TomlArray (List.map assertion_to_toml exprs))]
  | Or exprs ->
      TomlInlineTable [("or", TomlArray (List.map assertion_to_toml exprs))]
  | Not expr -> TomlInlineTable [("not", assertion_to_toml expr)]
  | True -> TomlBoolean true
  | False -> TomlBoolean false

let final_to_toml (test : Testrepr.t) =
  let assertion_entry = [("assertion", assertion_to_toml test.final)] in
  let kind_entry =
    match test.kind with
    | Exists -> []
    | Forall -> [("kind", Toml.TomlString "forall")]
    | NotExists -> [("kind", Toml.TomlString "notexists")]
  in
  Toml.TomlTable (assertion_entry @ kind_entry)

(** {1 Public API} *)

let to_toml (test : Testrepr.t) : Toml.t =
  TomlTable
    [ ("arch", TomlString test.arch);
      ("name", TomlString test.name);
      ("thread", threads_to_toml test.threads);
      ("memory", TomlTableArray (List.map memory_block_to_toml test.memory));
      ("final", final_to_toml test)
    ]

let to_string test = Toml.Printer.to_string ~force_table_arrays:true (to_toml test)

let to_file path test =
  let oc = open_out path in
  output_string oc (to_string test);
  close_out oc
