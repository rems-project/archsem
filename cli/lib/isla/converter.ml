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

(** Convert Isla IR to Testrepr.t.

    Pipeline: IR -> Assembler.assembly_input -> Assembler.assemble -> Testrepr.t.
    The converter fixes the VA layout for code/data symbols before calling the
    assembler. The assembler only emits code bytes and applies relocations for
    those preassigned addresses. The converter then evaluates terms and builds
    registers, memory, termination, and outcomes. *)

open Litmus
module RegValGen = Archsem.RegValGen
module Assertion = Litmus.Assertion

(* Fix lem/linksem dirty stuff *)
module Either = Stdlib.Either

(** {1 Setup} *)

(** {2 Config helpers} *)

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

(** {2 Evaluation errors} *)

type eval_context =
  | Location_init of string
  | Register_init of int * string
  | Final_assertion
  | Page_table_setup

exception Eval_error of string list * string

let eval_context_path = function
  | Location_init sym -> ["locations"; sym]
  | Register_init (tid, reg) -> ["thread"; string_of_int tid; "init"; reg]
  | Final_assertion -> ["final"; "assertion"]
  | Page_table_setup -> ["page_table_setup"]

(** {1 Conversion helpers} *)

(** {2 Term evaluation} *)

let eval_error context fmt =
  Printf.ksprintf
    (fun msg -> raise (Eval_error (eval_context_path context, msg)))
    fmt

let eval_term ~context ~lookup_addr term =
  try
    let value = Term.eval ~lookup_addr term in
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

(** {2 Address layout} *)

(* Explicit section addresses are already consumed before allocation starts.
   This assumes each assembled named section fits in one allocator page. *)
let reserved_section_addrs sections =
  List.filter_map (fun (sec : Ir.section) -> sec.address) sections

let thread_section_name tid = Printf.sprintf "__thread%d" tid

(* Build assembly input after assigning concrete addresses to every section and
   symbolic location. *)
let to_assembly_input allocator (ir : Ir.t) : Assembler.assembly_input =
  let code_sections =
    List.mapi
      (fun i (thread : Ir.thread) ->
         { Assembler.name = thread_section_name i;
           code = thread.code;
           addr = Allocator.alloc_page allocator
         }
       )
      ir.threads
  in
  let named_sections =
    List.map
      (fun (sec : Ir.section) ->
         let addr =
           match sec.address with
           | Some addr -> addr
           | None -> Allocator.alloc_page allocator
         in
         {Assembler.name = sec.sec_name; code = sec.code; addr}
       )
      ir.sections
  in
  let symbols =
    List.map
      (fun sym ->
         let addr = Allocator.alloc_page allocator in
         {Assembler.name = sym; addr}
       )
      ir.symbolic
  in
  {Assembler.sections = code_sections @ named_sections; symbols}

(** {2 Thread register construction} *)

let find_section name (asm_result : Assembler.assembly_result) =
  List.find
    (fun (s : Assembler.linked_section) -> s.name = name)
    asm_result.sections

(* Build per-thread initial register maps: PC + user init + config defaults. *)
let build_registers ~arch ~lookup_addr ~pc (start_pc : int) (thread : Ir.thread) =
  let pc_entry = (pc, RegValGen.Number (Z.of_int start_pc)) in
  let used_regs =
    List.map
      (fun (reg, value) ->
         let context = Register_init (thread.tid, reg) in
         let gen = RegValGen.Number (eval_term ~context ~lookup_addr value) in
         (reg, normalize_register_gen ~arch ~context reg gen)
       )
      thread.init
  in
  let base_regs = pc_entry :: used_regs in
  let has regs name = List.exists (fun (reg, _) -> reg = name) regs in
  let default_regs =
    List.filter_map
      (fun (reg, value) -> if has base_regs reg then None else Some (reg, value))
      (register_defaults ())
  in
  base_regs @ default_regs

let build_threads ~arch ~lookup_addr asm_result (threads : Ir.thread list) :
  Testrepr.thread list
  =
  let pc = pc_reg arch in
  List.mapi
    (fun tid (thread : Ir.thread) ->
       let sec = find_section (thread_section_name tid) asm_result in
       let regs = build_registers ~arch ~lookup_addr ~pc sec.addr thread in
       let breakpoints = [Z.of_int (sec.addr + Bytes.length sec.data)] in
       {Testrepr.regs; breakpoints}
     )
    threads

(** {2 Page table setup construction} *)

(* Build the page-table layout from concrete section/symbol VAs.
  Thread code pages are included so the DSL can request code mappings. *)
let build_page_table_setup ir allocator asm_result =
  match ir.Ir.page_table_setup with
  | [] -> None
  | page_table_setup -> (
      if ir.Ir.locations <> [] then
        eval_error Page_table_setup
          "page_table: [locations] is not supported with page_table_setup";
      let symbolic_vas = asm_result.Assembler.symbols in
      let code_pages =
        List.map
          (fun (thread : Ir.thread) ->
             let sec = find_section (thread_section_name thread.tid) asm_result in
             sec.addr
           )
          ir.Ir.threads
      in
      try
        Some
          (Page_table_builder.build ~arch:ir.arch ~allocator ~symbolic_vas
             ~code_pages page_table_setup
          )
      with Page_table_builder.Error msg -> eval_error Page_table_setup "%s" msg
    )

(* Terms may refer to VA-side symbols from assembly and PA-side aliases created
   by page_table_setup. *)
let build_lookup_addr asm_result page_table =
  let symbols_pa =
    match page_table with
    | None -> []
    | Some layout -> layout.Page_table_builder.symbols_pa
  in
  let symbols_addr = asm_result.Assembler.symbols @ symbols_pa in
  fun name ->
    match List.assoc_opt name symbols_addr with
    | Some addr -> addr
    | None -> Printf.ksprintf failwith "Symbol %s not found" name

(** {2 Memory construction} *)

(* Encode integer initialisers as fixed-size little-endian byte strings. *)
let init_bytes_of_value mem_size label value =
  if Z.numbits value > mem_size * 8 then
    Error.fatal "Number doesn't fit in symbol %s" label;
  let data = Bytes.make mem_size '\x00' in
  let bits = Z.to_bits value in
  Bytes.blit_string bits 0 data 0 (min mem_size (String.length bits));
  data

let build_code ~instruction_step (asm_result : Assembler.assembly_result) =
  List.map
    (fun (sec : Assembler.linked_section) ->
       { Testrepr.addr = sec.addr;
         step = instruction_step;
         data = sec.data;
         sym = Some sec.name;
         kind = Testrepr.Code
       }
     )
    asm_result.Assembler.sections

let data_memory_block ~step ?(kind = Testrepr.Data) ?symbol addr value :
  Testrepr.memory_block
  =
  let label = Option.value symbol ~default:(Printf.sprintf "0x%x" addr) in
  { Testrepr.addr;
    step;
    data = init_bytes_of_value step label value;
    sym = symbol;
    kind
  }

(* Build backing data blocks for declared symbolic locations. *)
let build_locations_memory ~mem_size ~symbols ~lookup_addr ~locations =
  List.map
    (fun (sym : Assembler.data_symbol) ->
       let value =
         List.assoc_opt sym.name locations
         |> Option.map (eval_term ~context:(Location_init sym.name) ~lookup_addr)
         |> Option.value ~default:Z.zero
       in
       data_memory_block ~step:mem_size ~symbol:sym.name sym.addr value
     )
    symbols

let build_page_table_memory ~mem_size page_table =
  let table_memory =
    List.map
      (fun (addr, value) ->
         data_memory_block ~step:Page_table_desc.entry_size
           ~kind:Testrepr.PageTable addr (Z.of_int64 value)
       )
      page_table.Page_table_builder.table_entries
  in
  let phys_memory =
    List.map
      (fun (sym, pa) ->
         let value =
           List.assoc_opt pa page_table.Page_table_builder.data_inits
           |> Option.value ~default:Z.zero
         in
         data_memory_block ~step:mem_size ~symbol:sym pa value
       )
      page_table.Page_table_builder.phys_symbols_pa
  in
  table_memory @ phys_memory

(* Build the final Testrepr memory from assembled code plus whichever data
   representation the test uses. *)
let build_memory
      ~mem_size
      ~data_symbols
      ~lookup_addr
      ~locations
      asm_result
      page_table
  =
  let code_memory =
    build_code ~instruction_step:(instruction_step ()) asm_result
  in
  let data_memory =
    match page_table with
    | None ->
        build_locations_memory ~mem_size ~symbols:data_symbols ~lookup_addr
          ~locations
    | Some page_table -> build_page_table_memory ~mem_size page_table
  in
  code_memory @ data_memory

(** {1 Public API} *)

let to_testrepr ~filename (ir : Ir.t) : Testrepr.t =
  let mem_size = default_memory_size () in
  let reserved_addrs = reserved_section_addrs ir.sections in
  let allocator = Allocator.make ~reserved:reserved_addrs () in
  let asm_input = to_assembly_input allocator ir in
  let asm_result = Assembler.assemble ~filename asm_input in
  let page_table = build_page_table_setup ir allocator asm_result in
  let lookup_addr = build_lookup_addr asm_result page_table in
  let threads = build_threads ~arch:ir.arch ~lookup_addr asm_result ir.threads in
  let memory =
    build_memory ~mem_size ~data_symbols:asm_input.symbols ~lookup_addr
      ~locations:ir.locations asm_result page_table
  in
  { arch = Litmus.Arch_id.to_string ir.arch;
    name = ir.name;
    threads;
    memory;
    kind = ir.kind;
    final =
      Assertion.map_cst
        (eval_term ~context:Final_assertion ~lookup_addr)
        ir.assertion
  }
