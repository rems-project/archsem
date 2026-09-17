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
    registers, memory, termination, and outcomes using one mutable evaluation
    state for each test. *)

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
  | Breakpoints of int
  | Final_assertion
  | Page_table_setup

exception Eval_error of string list * string

let eval_context_path = function
  | Location_init sym -> ["locations"; sym]
  | Register_init (tid, reg) -> ["thread"; string_of_int tid; "init"; reg]
  | Breakpoints tid -> ["thread"; string_of_int tid; "breakpoints"]
  | Final_assertion -> ["final"; "assertion"]
  | Page_table_setup -> ["page_table_setup"]

(** {1 Conversion helpers} *)

(** {2 Term evaluation} *)

let eval_error context fmt =
  Printf.ksprintf
    (fun msg -> raise (Eval_error (eval_context_path context, msg)))
    fmt

let eval_term ~context ~state term =
  try
    let value = Term.eval ~state term in
    match context with
    (* Final constants stay raw Z.t; registers read via bv_unsigned. *)
    | Final_assertion when Z.sign value < 0 ->
        eval_error context "final assertion values must be non-negative: %s"
          (Z.format "%#x" value)
    | Breakpoints _ when Z.sign value < 0 ->
        eval_error context "Breakpoint values must be non-negative: %s"
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

let symbolic_names ir =
  let add names name = if List.mem name names then names else names @ [name] in
  let rec collect names = function
    | [] -> names
    | Page_table_ast.Virtual stmt_names :: stmts ->
        collect (List.fold_left add names stmt_names) stmts
    | Page_table_ast.TableBlock {body; _} :: stmts ->
        collect (collect names body) stmts
    | _ :: stmts -> collect names stmts
  in
  collect ir.Ir.symbolic ir.Ir.page_table_setup

let checked_virtual_alignment alignment =
  let alignment =
    try Z.to_int alignment
    with Z.Overflow ->
      eval_error Page_table_setup "page_table: virtual alignment is out of range"
  in
  if alignment <= 0 || alignment mod Allocator.page_size <> 0 then
    eval_error Page_table_setup
      "page_table: virtual alignment must be a positive multiple of page size: %d"
      alignment;
  alignment

let checked_mapping_alignment level =
  try Page_table_desc.level_size level
  with Invalid_argument _ ->
    eval_error Page_table_setup "page_table: invalid mapping level: %d" level

let symbolic_va_alignments ir =
  let virtual_names = symbolic_names ir in
  let alignments = Hashtbl.create 32 in
  let request name alignment =
    let previous =
      Hashtbl.find_opt alignments name
      |> Option.value ~default:Allocator.page_size
    in
    Hashtbl.replace alignments name (max previous alignment)
  in
  let rec collect stmts =
    List.iter
      (function
        | Page_table_ast.AlignedVirtual {alignment; names} ->
            let alignment = checked_virtual_alignment alignment in
            List.iter
              (fun name ->
                 if not (List.mem name virtual_names) then
                   eval_error Page_table_setup "page_table: undeclared VA: %s"
                     name;
                 request name alignment
               )
              names
        | Page_table_ast.Mapping {va_name; level = Some level; _} ->
            request va_name (checked_mapping_alignment level)
        | Page_table_ast.TableBlock {body; _} -> collect body
        | _ -> ()
        )
      stmts
  in
  collect ir.Ir.page_table_setup;
  List.map
    (fun name ->
       ( name,
         Hashtbl.find_opt alignments name
         |> Option.value ~default:Allocator.page_size
       )
     )
    virtual_names

let make_arena ?(reserved = []) base =
  assert (base land 0x1FFFFF == 0);
  Allocator.make ~base ~limit:(base + Allocator.big_size) ~reserved ()

(* Layout:
   - Code: 0-2 MiB
   - Page tables: 2-4 MiB
   - Data: >= 4 MiB *)
let table_base = Allocator.big_size

let data_base = table_base + Allocator.big_size

(* Named roots occupy fixed pages in the shared table arena. Reserve those
   pages before allocating the default root and child tables. The builder
   validates the root addresses. *)
let rec table_root_pages = function
  | [] -> []
  | Page_table_ast.TableBlock {base; body; _} :: stmts ->
      Z.to_int base :: (table_root_pages body @ table_root_pages stmts)
  | _ :: stmts -> table_root_pages stmts

(* Build assembly input after assigning concrete addresses to every section and
   symbolic location. *)
let to_assembly_input ~code_allocator ~symbol_allocator (ir : Ir.t) :
  Assembler.assembly_input
  =
  let code_sections =
    List.mapi
      (fun i (thread : Ir.thread) ->
         { Assembler.name = thread_section_name i;
           code = thread.code;
           addr = Allocator.alloc_page code_allocator
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
           | None -> Allocator.alloc_page code_allocator
         in
         {Assembler.name = sec.sec_name; code = sec.code; addr}
       )
      ir.sections
  in
  let symbols =
    List.map
      (fun (name, alignment) ->
         let addr =
           Allocator.alloc_aligned symbol_allocator ~size:alignment ~alignment
         in
         {Assembler.name; addr}
       )
      (symbolic_va_alignments ir)
  in
  {Assembler.sections = code_sections @ named_sections; symbols}

let assemble ~filename ~state ~code_allocator ~symbol_allocator ir =
  let input = to_assembly_input ~code_allocator ~symbol_allocator ir in
  let result = Assembler.assemble ~filename input in
  List.iter
    (fun (name, addr) -> Eval_state.add_virtual state name addr)
    result.symbols;
  (input, result)

(** {2 Thread register construction} *)

let find_section name (asm_result : Assembler.assembly_result) =
  List.find
    (fun (s : Assembler.linked_section) -> s.name = name)
    asm_result.sections

(* Build per-thread initial register maps: PC + user init + config defaults. *)
let build_registers
      ~arch
      ?page_table_root
      ~state
      ~pc
      (start_pc : int)
      (thread : Ir.thread)
  =
  let pc_entry = (pc, RegValGen.Number (Z.of_int start_pc)) in
  let used_regs =
    List.map
      (fun (reg, value) ->
         let context = Register_init (thread.tid, reg) in
         let gen = RegValGen.Number (eval_term ~context ~state value) in
         (reg, normalize_register_gen ~arch ~context reg gen)
       )
      thread.regs
  in
  let base_regs = pc_entry :: used_regs in
  let has regs name = List.exists (fun (reg, _) -> reg = name) regs in
  let base_regs =
    match page_table_root with
    | Some root when not (has base_regs "TTBR0_EL1") ->
        base_regs @ [("TTBR0_EL1", RegValGen.Number (Z.of_int root))]
    | _ -> base_regs
  in
  let default_regs =
    List.filter_map
      (fun (reg, value) -> if has base_regs reg then None else Some (reg, value))
      (register_defaults ())
  in
  base_regs @ default_regs

let build_threads
      ~arch
      ?page_table_root
      ~state
      asm_result
      (threads : Ir.thread list) : Testrepr.thread list
  =
  let pc = pc_reg arch in
  List.mapi
    (fun tid (thread : Ir.thread) ->
       let sec = find_section (thread_section_name tid) asm_result in
       let regs =
         build_registers ~arch ?page_table_root ~state ~pc sec.addr thread
       in
       let breakpoints =
         let context = Breakpoints tid in
         Z.of_int (sec.addr + Bytes.length sec.data)
         :: List.map (eval_term ~context ~state) thread.breakpoints
       in
       {Testrepr.regs; breakpoints}
     )
    threads

(** {2 Page table setup construction} *)

(* Build the page-table layout from concrete section/symbol VAs. *)
let build_page_table_setup
      ir
      ~symbol_allocator
      ~table_allocator
      ~table_block
      ~state
  =
  if ir.Ir.locations <> [] then
    eval_error Page_table_setup
      "page_table: [locations] is not supported with page_table_setup";
  try
    Page_table_builder.build ~arch:ir.arch ~symbol_allocator ~table_allocator
      ~table_block ~state ir.page_table_setup
  with Page_table_builder.Error msg -> eval_error Page_table_setup "%s" msg

(** {2 Memory construction} *)

let symbol_size ~default symbol_sizes sym =
  List.assoc_opt sym symbol_sizes |> Option.value ~default

(* Encode integer initialisers as fixed-size little-endian byte strings. *)
let init_bytes_of_value mem_size label value =
  let bit_width = mem_size * 8 in
  if Z.numbits value > bit_width then
    Error.fatal "Number doesn't fit in symbol %s" label;
  let value = Z.extract value 0 bit_width in
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
let build_locations_memory
      ~default_mem_size
      ~symbol_sizes
      ~symbols
      ~state
      ~locations
  =
  List.map
    (fun (sym : Assembler.data_symbol) ->
       let mem_size =
         symbol_size ~default:default_mem_size symbol_sizes sym.name
       in
       let value =
         List.assoc_opt sym.name locations
         |> Option.map (eval_term ~context:(Location_init sym.name) ~state)
         |> Option.value ~default:Z.zero
       in
       data_memory_block ~step:mem_size ~symbol:sym.name sym.addr value
     )
    symbols

let build_page_table_memory ~default_mem_size ~symbol_sizes ~entries page_table =
  let table_memory =
    Hashtbl.fold
      (fun addr value memory ->
         data_memory_block ~step:Page_table_desc.entry_size
           ~kind:Testrepr.PageTable addr (Z.of_int64 value)
         :: memory
       )
      entries []
    |> List.sort (fun (a : Testrepr.memory_block) b -> Int.compare a.addr b.addr)
  in
  let phys_memory =
    Hashtbl.fold
      (fun sym pa memory ->
         let mem_size = symbol_size ~default:default_mem_size symbol_sizes sym in
         let value =
           Hashtbl.find_opt page_table.Page_table_builder.data_inits pa
           |> Option.value ~default:Z.zero
         in
         data_memory_block ~step:mem_size ~symbol:sym pa value :: memory
       )
      page_table.Page_table_builder.data_symbols_pa []
    |> List.sort (fun (a : Testrepr.memory_block) b -> Int.compare a.addr b.addr)
  in
  table_memory @ phys_memory

(* Build the final Testrepr memory from assembled code plus whichever data
   representation the test uses. *)
let build_memory
      ~default_mem_size
      ~symbol_sizes
      ~data_symbols
      ~state
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
        build_locations_memory ~default_mem_size ~symbol_sizes
          ~symbols:data_symbols ~state ~locations
    | Some page_table ->
        let entries = Option.get state.Eval_state.page_table in
        build_page_table_memory ~default_mem_size ~symbol_sizes ~entries
          page_table
  in
  code_memory @ data_memory

(** {1 Public API} *)

let to_testrepr ~filename (ir : Ir.t) : Testrepr.t =
  let state = Eval_state.create () in
  let default_mem_size = default_memory_size () in
  let (asm_input, asm_result, page_table) =
    if ir.page_table_setup = [] then
      let allocator =
        Allocator.make ~base:0
          ~reserved:(0 :: reserved_section_addrs ir.sections)
          ()
      in
      let (asm_input, asm_result) =
        assemble ~filename ~state ~code_allocator:allocator
          ~symbol_allocator:allocator ir
      in
      (asm_input, asm_result, None)
    else
      let reserved_code_pages = reserved_section_addrs ir.sections in
      let code_allocator = make_arena ~reserved:(0 :: reserved_code_pages) 0 in
      let symbol_allocator = Allocator.make ~base:data_base () in
      let table_allocator =
        make_arena ~reserved:(table_root_pages ir.page_table_setup) table_base
      in
      let (asm_input, asm_result) =
        assemble ~filename ~state ~code_allocator ~symbol_allocator ir
      in
      let page_table =
        build_page_table_setup ir ~symbol_allocator ~table_allocator
          ~table_block:table_base ~state
      in
      (asm_input, asm_result, Some page_table)
  in
  let page_table_root =
    Option.bind page_table (fun layout -> layout.Page_table_builder.default_root)
  in
  let threads =
    build_threads ~arch:ir.arch ?page_table_root ~state asm_result ir.threads
  in
  let memory =
    build_memory ~default_mem_size ~symbol_sizes:ir.sizes
      ~data_symbols:asm_input.symbols ~state ~locations:ir.locations asm_result
      page_table
  in
  { arch = Litmus.Arch_id.to_string ir.arch;
    name = ir.name;
    threads;
    memory;
    kind = ir.kind;
    final =
      Assertion.map_cst (eval_term ~context:Final_assertion ~state) ir.assertion
  }
