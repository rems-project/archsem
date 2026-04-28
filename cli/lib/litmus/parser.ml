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
    - [[outcome]]: Expected observable/unobservable final condition

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

(** {2 Register final condition parsing} *)

(** Parse a requirement from TOML into Testrepr.reg_requirement *)
let parse_reg_requirement (toml : Toml.t) : Testrepr.reg_requirement =
  match toml with
  | TomlTable pairs | TomlInlineTable pairs -> (
    match (List.assoc_opt "op" pairs, List.assoc_opt "val" pairs) with
    | (Some (TomlString "eq"), Some v) -> Testrepr.ReqEq (toml_to_gen v)
    | (Some (TomlString "ne"), Some v) -> Testrepr.ReqNe (toml_to_gen v)
    | (Some (TomlString op), _) ->
        failwith ("[[outcome]] unknown requirement op: " ^ op)
    | _ -> Testrepr.ReqEq (toml_to_gen toml)
  )
  | _ -> Testrepr.ReqEq (toml_to_gen toml)

(** Parse a condition block into thread conditions with string keys *)
let parse_reg_cond toml : (int * (string * Testrepr.reg_requirement) list) list =
  let regs_table =
    match Toml.find_opt toml Toml.get_table ["regs"] with
    | Some regs_table -> regs_table
    | None -> Toml.get_table toml
  in
  regs_table
  |> List.filter_map (fun (tid_str, regs) ->
    match int_of_string_opt tid_str with
    | None -> None
    | Some tid ->
        let reqs = Toml.get_table_values parse_reg_requirement regs in
        Some (tid, reqs)
  )

(** {2 Memory final condition parsing} *)

(** Parse all [[outcome]] blocks into final conditions *)
let parse_mem_requirement (toml : Toml.t) : Testrepr.mem_requirement =
  match toml with
  | TomlTable pairs | TomlInlineTable pairs -> (
    match (List.assoc_opt "op" pairs, List.assoc_opt "val" pairs) with
    | (Some (TomlString "eq"), Some v) -> MemEq (Toml.get_Z v)
    | (Some (TomlString "ne"), Some v) -> MemNe (Toml.get_Z v)
    | (_, _) ->
        failwith
          ("[[outcome]] unknown memory requirement: "
         ^ Toml.Printer.to_string toml
          )
  )
  | _ -> MemEq (Toml.get_Z toml)

let parse_mem_entry mem sym toml : Testrepr.mem_cond =
  let block =
    try Testrepr.mem_by_sym sym mem
    with Not_found ->
      failwith ("[[outcome]].mem." ^ sym ^ " not found in memory")
  in
  let req = parse_mem_requirement toml in
  {sym; addr = block.addr; size = Testrepr.block_size block; req}

let parse_mem_conds mem toml : Testrepr.mem_cond list =
  let parse_mem_cond toml =
    Toml.get_table toml |> List.map (fun (sym, v) -> parse_mem_entry mem sym v)
  in
  Toml.find_or ~default:[] toml parse_mem_cond ["mem"]

let parse_test_finals mem toml : Testrepr.final_cond list =
  let parse_test_final toml =
    let parse_with_mem toml =
      let regs = parse_reg_cond toml in
      let mem = parse_mem_conds mem toml in
      (regs, mem)
    in
    match
      ( Toml.find_opt toml parse_with_mem ["observable"],
        Toml.find_opt toml parse_with_mem ["unobservable"]
      )
    with
    | (Some (regs, mem), None) -> Testrepr.Observable (regs, mem)
    | (None, Some (regs, mem)) -> Testrepr.Unobservable (regs, mem)
    | (Some _, Some _) ->
        failwith "[[outcome]] cannot have both observable and unobservable"
    | (None, None) ->
        failwith "[[outcome]] must have observable or unobservable key"
  in
  Toml.find toml (Toml.get_array parse_test_final) ["outcome"]

let resolve_mem_conds memory (mcs : Testrepr.mem_cond list) =
  let sym_table =
    List.filter_map
      (fun (block : Testrepr.memory_block) ->
         Option.map (fun sym -> (sym, (block.addr, block.step))) block.sym
       )
      memory
  in
  List.map
    (fun (mc : Testrepr.mem_cond) ->
       let (addr, size) =
         match List.assoc_opt mc.sym sym_table with
         | Some (addr, step) -> (addr, if mc.size = 0 then step else mc.size)
         | None -> failwith ("[[outcome]] unknown memory symbol: " ^ mc.sym)
       in
       {mc with addr; size}
     )
    mcs

let parse_to_testrepr : Toml.t -> Testrepr.t =
 fun toml ->
  let memory = parse_test_memory toml in
  { Testrepr.arch = Toml.find toml Toml.get_string ["arch"];
    name = Toml.find toml Toml.get_string ["name"];
    registers = parse_test_registers toml;
    memory;
    term_cond = parse_test_termcond toml;
    finals = parse_test_finals memory toml
  }
