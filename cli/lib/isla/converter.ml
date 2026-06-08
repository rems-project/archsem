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

(** Convert isla IR to Testrepr.t.

    Pipeline: IR -> assembly_input -> Assembler.assemble -> Testrepr.t.
    Config supplies architecture defaults, the assembler returns linked code/data
    addresses, and the final conversion builds memory, registers, termination,
    and outcomes. *)

open Litmus
module RegValGen = Archsem.RegValGen
module Assertion = Litmus.Assertion

(* Fix lem/linksem dirty stuff *)
module Either = Stdlib.Either

(** {1 Config helpers} *)

let pc_reg arch =
  match arch with
  | Litmus.Arch_id.Arm -> Archsem.Arm.Reg.to_string Archsem.Arm.Reg.pc
  | Litmus.Arch_id.X86 -> Archsem.X86.Reg.to_string Archsem.X86.Reg.pc

let register_defaults =
  Config.make_getter ~default:[]
    (Toml.get_table_values Litmus.Parser.toml_to_gen)
    ["registers"; "defaults"]

let instruction_step =
  Config.make_getter Toml.get_positive ["assembler"; "instruction_step"]

let default_memory_size =
  Config.make_getter Toml.get_positive ["isla"; "default_memory_size"]

(** {1 IR to assembly_input} *)

let init_bytes_of_value mem_size sym value =
  if Z.numbits value > mem_size * 8 then
    Error.fatal "Number doesn't fit in symbol %s" sym;
  let data = Bytes.make mem_size '\x00' in
  let bits = Z.to_bits value in
  Bytes.blit_string bits 0 data 0 (min mem_size (String.length bits));
  data

type term_eval_context =
  | Location_init of string
  | Register_init of int * string
  | Final_assertion

exception Term_eval_error of string list * string

let term_eval_context_path = function
  | Location_init sym -> ["locations"; sym]
  | Register_init (tid, reg) -> ["thread"; string_of_int tid; "init"; reg]
  | Final_assertion -> ["final"; "assertion"]

let eval_error context fmt =
  Printf.ksprintf
    (fun msg -> raise (Term_eval_error (term_eval_context_path context, msg)))
    fmt

let eval_term ~context ~resolve_sym term =
  try
    let value = Term.eval ~resolve_sym term in
    match context with
    (* Final constants stay raw Z.t; registers read via bv_unsigned. *)
    | Final_assertion when Z.sign value < 0 ->
        eval_error context "final assertion values must be non-negative: %s"
          (Z.format "%#x" value)
    (* Memory values are converted with Z.to_bits. *)
    | Location_init _ when Z.sign value < 0 ->
        eval_error context "negative memory data is not allowed: %s"
          (Z.format "%#x" value)
    | _ -> value
  with Failure msg -> eval_error context "%s" msg

let normalize_register_gen ~arch ~context reg_name gen =
  try
    match arch with
    | Litmus.Arch_id.Arm ->
        Archsem.Arm.RegVal.(to_gen (of_string_gen reg_name gen))
    | Litmus.Arch_id.X86 ->
        Archsem.X86.RegVal.(to_gen (of_string_gen reg_name gen))
  with Failure msg -> eval_error context "%s" msg

let data_symbol_of_value ~context ~resolve_sym mem_size sym value =
  let value = eval_term ~context ~resolve_sym value in
  {Assembler.name = sym; init_bytes = init_bytes_of_value mem_size sym value}

let to_assembly_input (ir : Ir.t) : Assembler.assembly_input =
  let mem_size = default_memory_size () in
  let code_sections =
    List.mapi
      (fun i (thread : Ir.thread) ->
         { Assembler.name = Printf.sprintf "thread%d" i;
           code = thread.code;
           fixed_addr = None
         }
       )
      ir.threads
  in
  let data_symbols =
    List.map
      (fun sym ->
         let init_value =
           List.assoc_opt sym ir.locations |> Option.value ~default:Term.zero
         in
         (* A symbol-valued initializer needs the post-link symbol address, but
            the assembler only needs the block size to compute layout here. *)
         data_symbol_of_value ~context:(Location_init sym)
           ~resolve_sym:(fun _ -> 0)
           mem_size sym init_value
       )
      ir.symbolic
  in
  let fixed_sections =
    List.map
      (fun (sec : Ir.section) ->
         { Assembler.name = sec.sec_name;
           code = sec.code;
           fixed_addr = Some sec.address
         }
       )
      ir.sections
  in
  {sections = code_sections @ fixed_sections; symbols = data_symbols}

let resolve_data_symbols
      (asm_result : Assembler.assembly_result)
      (ir : Ir.t)
      mem_size
  =
  List.map
    (fun sym ->
       let init_value =
         List.assoc_opt sym ir.locations |> Option.value ~default:Term.zero
       in
       data_symbol_of_value ~context:(Location_init sym)
         ~resolve_sym:(Assembler.resolve_symbol asm_result)
         mem_size sym init_value
     )
    ir.symbolic

(** {1 Memory, registers, and termination} *)

(** Convert linked sections and data symbols into Testrepr memory blocks.
    User-named sections (those listed in [user_section_names]) carry
    [sym = Some name]; auto-generated thread sections do not. *)
let build_memory
      ~data_symbols
      ~user_section_names
      (asm_result : Assembler.assembly_result)
  =
  let code_step = instruction_step () in
  let mem_size = default_memory_size () in
  let code_memory =
    List.map
      (fun (sec : Assembler.linked_section) ->
         let sym =
           if List.mem sec.name user_section_names then Some sec.name else None
         in
         { Testrepr.addr = sec.addr;
           step = code_step;
           data = sec.data;
           sym;
           kind = Testrepr.Code
         }
       )
      asm_result.sections
  in
  let data_memory =
    List.map
      (fun (ds : Assembler.data_symbol) ->
         { Testrepr.addr = Assembler.resolve_symbol asm_result ds.name;
           step = mem_size;
           data = ds.init_bytes;
           sym = Some ds.name;
           kind = Testrepr.Data
         }
       )
      data_symbols
  in
  code_memory @ data_memory

let find_section name (asm_result : Assembler.assembly_result) =
  List.find
    (fun (s : Assembler.linked_section) -> s.name = name)
    asm_result.sections

(** Build per-thread initial register maps: PC + user init + config defaults. *)
let build_registers ~arch ~resolve_sym ~pc (start_pc : int) (thread : Ir.thread) =
  let pc_entry = (pc, RegValGen.Number (Z.of_int start_pc)) in
  let used_regs =
    List.map
      (fun (reg, value) ->
         let context = Register_init (thread.tid, reg) in
         let gen = RegValGen.Number (eval_term ~context ~resolve_sym value) in
         (reg, normalize_register_gen ~arch ~context reg gen)
       )
      thread.init
  in
  let explicit_regs = pc_entry :: used_regs in
  let has name = List.exists (fun (reg, _) -> reg = name) explicit_regs in
  let default_regs =
    List.filter_map
      (fun (reg, value) -> if has reg then None else Some (reg, value))
      (register_defaults ())
  in
  explicit_regs @ default_regs

let build_threads ~arch ~resolve_sym asm_result (threads : Ir.thread list) :
  Testrepr.thread list
  =
  let pc = pc_reg arch in
  List.mapi
    (fun tid (thread : Ir.thread) ->
       assert (tid == thread.tid);
       (* Should have been checked before *)
       let sec = find_section (Printf.sprintf "thread%d" tid) asm_result in
       let regs = build_registers ~arch ~resolve_sym ~pc sec.addr thread in
       let breakpoints = [Z.of_int (sec.addr + Bytes.length sec.data)] in
       {Testrepr.regs; breakpoints}
     )
    threads

(** {1 Orchestration} *)

let to_testrepr (ir : Ir.t) : Testrepr.t =
  let mem_size = default_memory_size () in
  let asm_input = to_assembly_input ir in
  let asm_result = Assembler.assemble asm_input in
  let data_symbols = resolve_data_symbols asm_result ir mem_size in
  let resolve_sym sym = Assembler.resolve_symbol asm_result sym in
  let threads = build_threads ~arch:ir.arch ~resolve_sym asm_result ir.threads in
  let user_section_names =
    List.map (fun (s : Ir.section) -> s.sec_name) ir.sections
  in
  let memory = build_memory ~data_symbols ~user_section_names asm_result in
  { arch = Litmus.Arch_id.to_string ir.arch;
    name = ir.name;
    threads;
    memory;
    kind = ir.kind;
    final =
      Assertion.map_cst
        (eval_term ~context:Final_assertion ~resolve_sym)
        ir.assertion
  }
