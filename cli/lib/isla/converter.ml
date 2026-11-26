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

    Pipeline:
    - Reserve the pages of explicitly placed sections and table roots.
    - Collect the data symbols (symbolic, then page-table [virtual]/[physical]
      declarations) and their alignment constraints, allocate non-offset symbol,
      compute offset symbols, and finally register the symbols in the test's
      mutable evaluation state.
    - Allocate the code sections and assemble them against those symbols. The
      assembler only emits code bytes and applies relocations.
    - Build page tables, memory, registers, termination, and outcomes. *)

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

(** Return the register defaults of [registers.defaults], overridden key by key
    by [profile.p.registers.defaults] for the profile selected for the test *)
let register_defaults =
  Config.make_getter_selected_profile ~default:[]
    (Toml.get_table_values Litmus.Parser.toml_to_gen)
    (fun base overrides ->
       List.filter (fun (reg, _) -> not (List.mem_assoc reg overrides)) base
       @ overrides
     )
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

let eval_error_at path fmt =
  Printf.ksprintf (fun msg -> raise (Eval_error (path, msg))) fmt

let eval_error context fmt = eval_error_at (eval_context_path context) fmt

let check_symbol_name path name =
  if not (Lexer.is_ident name) then
    eval_error_at path
      "Symbol %S is invalid: names must start with a letter or '_', only contain \
       letters, digits and '_', and not be a keyword"
       name

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

(** {2 Data symbols} *)

type symbol_kind =
  | Physical
  | Virtual

(* Data symbols declared by [symbolic] and by the [virtual] and [physical]
   page-table statements: symbolic first, then in page-table setup order.
   Symbolic symbols are physical without page tables, and virtual with them.
   Fails if a symbol name is invalid or declared twice. *)
let get_data_symbols (ir : Ir.t) =
  let add path kind name symbols =
    check_symbol_name path name;
    if List.exists (fun (_, n) -> n = name) symbols then
      eval_error_at path "Symbol %s is already defined" name;
    (kind, name) :: symbols
  in
  let add_all path kind names symbols =
    List.fold_left (fun symbols name -> add path kind name symbols) symbols names
  in
  let rec collect symbols = function
    | Page_table_ast.Virtual names ->
        add_all ["page_table_setup"] Virtual names symbols
    | Page_table_ast.Physical names ->
        add_all ["page_table_setup"] Physical names symbols
    | Page_table_ast.TableBlock {body; _} -> List.fold_left collect symbols body
    | _ -> symbols
  in
  let symbolic_kind = if ir.page_table_setup = [] then Physical else Virtual in
  let symbols = add_all ["symbolic"] symbolic_kind ir.symbolic [] in
  List.rev (List.fold_left collect symbols ir.page_table_setup)

(* Data symbols backed by memory blocks: [symbolic] without page tables, the
   [physical] declarations with them. *)
let get_physical_data_symbols ir =
  List.filter_map
    (function (Physical, name) -> Some name | (Virtual, _) -> None)
    (get_data_symbols ir)

let get_all_data_symbols ir = List.map snd (get_data_symbols ir)

(** {2 Alignment constraints} *)

let checked_explicit_alignment alignment =
  if not (Z.fits_int alignment) then
    eval_error Page_table_setup "page_table: alignment is out of range: %s"
      (Z.to_string alignment);
  if Z.sign alignment <= 0 || Z.popcount alignment <> 1 then
    eval_error Page_table_setup "page_table: alignment must be a power of two: %s"
      (Z.to_string alignment);
  Z.to_int alignment

let checked_mapping_alignment level =
  try Page_table_desc.level_size level
  with Invalid_argument _ ->
    eval_error Page_table_setup "page_table: invalid mapping level: %d" level

(* Collect the alignment constraints of the page-table setup, on both virtual
   and physical symbols. Requests are combined with [max], which satisfies all
   of them as alignments are powers of two. Explicit [aligned] constraints must
   be on [declared] data symbols. *)
let get_alignment_constraints ~declared (ir : Ir.t) =
  let alignments = Hashtbl.create 32 in
  let request name alignment =
    match Hashtbl.find_opt alignments name with
    | Some previous -> Hashtbl.replace alignments name (max previous alignment)
    | None -> Hashtbl.add alignments name alignment
  in
  let rec collect = function
    | Page_table_ast.AlignedVirtual {alignment; names} ->
        let alignment = checked_explicit_alignment alignment in
        List.iter
          (fun name ->
             if not (List.mem name declared) then
               eval_error Page_table_setup "page_table: undeclared symbol: %s"
                 name;
             request name alignment
           )
          names
    (* Table mappings do not require larger allocations. *)
    | Page_table_ast.Mapping {target = Page_table_ast.Table _; _} -> ()
    | Page_table_ast.Mapping {va; target; level = Some level; _} -> (
        let alignment = checked_mapping_alignment level in
        (match va with Term.Sym name -> request name alignment | _ -> ());
        match target with
        | Page_table_ast.PaName name -> request name alignment
        | _ -> ()
      )
    | Page_table_ast.TableBlock {body; _} -> List.iter collect body
    | _ -> ()
  in
  List.iter collect ir.page_table_setup;
  alignments

(** {2 Reserved pages} *)

(* Layout:
   - Code: 0-2 MiB
   - Page tables: 2-4 MiB
   - Data: >= 4 MiB *)
let table_base = Allocator.big_size

let data_base = table_base + Allocator.big_size

(** Lists all explicit table roots in the page table language,
    [[("name", addr)]] *)
let rec explicit_table_roots = function
  | [] -> []
  | Page_table_ast.TableBlock {name; base; body; _} :: stmts -> (
      let nested = explicit_table_roots body @ explicit_table_roots stmts in
      match base with
      | Some base -> (name, Z.to_int base) :: nested
      | None -> nested
    )
  | _ :: stmts -> explicit_table_roots stmts

(** List all pre-reserved pages:
    - Page 0
    - All explicit code sections
    - All explicit page table roots *)
let reserved_pages (ir : Ir.t) =
  (0 :: List.filter_map (fun (sec : Ir.section) -> sec.address) ir.sections)
  @ List.map snd (explicit_table_roots ir.page_table_setup)

let in_block base pages =
  List.filter (fun addr -> base <= addr && addr < base + Allocator.big_size) pages

let make_arena ~reserved base =
  assert (base land 0x1FFFFF == 0);
  Allocator.make ~base ~limit:(base + Allocator.big_size)
    ~reserved:(in_block base reserved) ()

(** {2 Address allocation} *)

let thread_section_name tid = Printf.sprintf "__thread%d" tid

(* Place each thread and named section on its own page, except named sections
   with an explicit address. *)
let allocate_code_sections allocator (ir : Ir.t) : Assembler.section list =
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
         check_symbol_name ["section"; sec.sec_name] sec.sec_name;
         let addr =
           match sec.address with
           | Some addr -> addr
           | None -> Allocator.alloc_page allocator
         in
         {Assembler.name = sec.sec_name; code = sec.code; addr}
       )
      ir.sections
  in
  code_sections @ named_sections

let alloc_aligned allocator alignment =
  Allocator.alloc_aligned allocator ~size:alignment ~alignment

let is_offset (ir : Ir.t) name = List.mem_assoc name ir.offsets

(* Register each offset symbol at its base address plus its offset. Offset
   symbols are declared like other data symbols, and their bases are symbols
   allocated before assembly that are not offset symbols themselves. *)
let allocate_offsets ~state ~declared (ir : Ir.t) =
  List.iter
    (fun (name, (base, offset)) ->
       let path = ["offsets"; name] in
       if not (List.mem name declared) then
         eval_error_at path "Offset symbol %s is not declared" name;
       if is_offset ir base then
         eval_error_at path "Offset base %s is an offset symbol" base;
       let addr =
         match Hashtbl.find_opt state.Eval_state.symbols base with
         | Some addr when addr <= max_int - offset -> addr + offset
         | Some _ -> eval_error_at path "Offset address is out of range"
         | None -> eval_error_at path "Offset base %s is not allocated" base
       in
       try Eval_state.add_symbol state name addr
       with Failure msg -> eval_error_at path "%s" msg
     )
    ir.offsets

(* Allocate every data symbol from [base], aligned to its constraint and to at
   least a page, and register it in [state]. Offset symbols are registered after
   the other data symbols. Returns the allocator. *)
let allocate_data_symbols ~state ~reserved ~base (ir : Ir.t) =
  let allocator = Allocator.make ~base ~reserved () in
  let declared = get_all_data_symbols ir in
  let alignments = get_alignment_constraints ~declared ir in
  List.iter
    (fun name ->
       if not (is_offset ir name) then
         let alignment =
           Hashtbl.find_opt alignments name
           |> Option.fold ~none:Allocator.page_size ~some:(max Allocator.page_size)
         in
         let addr = alloc_aligned allocator alignment in
         try Eval_state.add_symbol state name addr
         with Failure msg -> eval_error Page_table_setup "%s" msg
     )
    declared;
  allocate_offsets ~state ~declared ir;
  allocator

(* Allocate every data symbol and register it in [state]. Without page tables,
   data symbols and code sections share one allocator from address 0. With page
   tables, table roots with an explicit base are registered first, then data
   symbols are allocated in the data region. Returns the allocator for the code
   sections and, with page tables, the addresses of the physical symbols. *)
let allocate_symbols ~state ~reserved (ir : Ir.t) =
  if ir.page_table_setup = [] then
    (allocate_data_symbols ~state ~reserved ~base:0 ir, None)
  else (
    List.iter
      (fun (name, base) ->
         try Eval_state.add_symbol state name base
         with Failure msg -> eval_error Page_table_setup "%s" msg
       )
      (explicit_table_roots ir.page_table_setup);
    ignore (allocate_data_symbols ~state ~reserved ~base:data_base ir);
    let data_symbols_pa = Hashtbl.create 32 in
    List.iter
      (fun name ->
         Hashtbl.add data_symbols_pa name (Eval_state.lookup_addr state name)
       )
      (get_physical_data_symbols ir);
    (make_arena ~reserved 0, Some data_symbols_pa)
  )

(** {2 Assembly} *)

(* Allocate the code sections and assemble them with a data symbol for every
   symbol in [state]. The assembler rejects code that redefines a data symbol.
   Code-defined symbols are added to [state]. *)
let assemble ~filename ~state ~code_allocator (ir : Ir.t) =
  let sections = allocate_code_sections code_allocator ir in
  let symbols =
    Hashtbl.fold
      (fun name addr symbols -> {Assembler.name; addr} :: symbols)
      state.Eval_state.symbols []
    |> List.sort compare
  in
  let result =
    try
      let result = Assembler.assemble ~filename {sections; symbols} in
      List.iter
        (fun (name, addr) -> Eval_state.add_symbol state name addr)
        result.symbols;
      result
    with Failure msg -> eval_error_at ["code"] "%s" msg
  in
  (* Assembly preserves input order: threads followed by named sections. *)
  List.iteri
    (fun i (sec : Assembler.linked_section) ->
       let size = Bytes.length sec.data in
       if size > Allocator.page_size then
         let path =
           if i < List.length ir.threads then ["thread"; string_of_int i; "code"]
           else ["section"; sec.name; "code"]
         in
         eval_error_at path
           "Code section %s is %d bytes; expected at most %d bytes" sec.name size
           Allocator.page_size
     )
    result.sections;
  result

(** {2 Thread register construction} *)

let find_section name (asm_result : Assembler.assembly_result) =
  List.find
    (fun (s : Assembler.linked_section) -> s.name = name)
    asm_result.sections

(* Build per-thread initial register maps: PC + user init + config defaults. *)
let build_registers
      ~arch
      ~page_table_setup
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
      (register_defaults ~page_table_setup)
  in
  base_regs @ default_regs

let build_threads
      ~arch
      ~page_table_setup
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
         build_registers ~arch ~page_table_setup ?page_table_root ~state ~pc
           sec.addr thread
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

(* Build the page-table layout from concrete symbol addresses. *)
let build_page_table_setup ir ~reserved ~data_symbols_pa ~state =
  if ir.Ir.locations <> [] then
    eval_error Page_table_setup
      "page_table: [locations] is not supported with page_table_setup";
  try
    Page_table_builder.build ~arch:ir.arch ~data_symbols_pa
      ~table_allocator:(make_arena ~reserved table_base)
      ~table_block:table_base ~state ir.page_table_setup
  with Page_table_builder.Error msg | Failure msg ->
    eval_error Page_table_setup "%s" msg

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

(* Build backing data blocks for physical data symbols. *)
let build_locations_memory
      ~default_mem_size
      ~symbol_sizes
      ~physical
      ~state
      ~locations
  =
  List.map
    (fun sym ->
       let mem_size = symbol_size ~default:default_mem_size symbol_sizes sym in
       let value =
         List.assoc_opt sym locations
         |> Option.map (eval_term ~context:(Location_init sym) ~state)
         |> Option.value ~default:Z.zero
       in
       data_memory_block ~step:mem_size ~symbol:sym
         (Eval_state.lookup_addr state sym)
         value
     )
    physical

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
      ~physical
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
        build_locations_memory ~default_mem_size ~symbol_sizes ~physical ~state
          ~locations
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
  let reserved = reserved_pages ir in
  let (code_allocator, data_symbols_pa) = allocate_symbols ~state ~reserved ir in
  let asm_result = assemble ~filename ~state ~code_allocator ir in
  let page_table =
    Option.map
      (fun data_symbols_pa ->
         build_page_table_setup ir ~reserved ~data_symbols_pa ~state
       )
      data_symbols_pa
  in
  let page_table_root =
    Option.bind page_table (fun layout -> layout.Page_table_builder.default_root)
  in
  let threads =
    build_threads ~arch:ir.arch ~page_table_setup:(ir.page_table_setup <> [])
      ?page_table_root ~state asm_result ir.threads
  in
  let memory =
    build_memory ~default_mem_size ~symbol_sizes:ir.sizes
      ~physical:(get_physical_data_symbols ir)
      ~state ~locations:ir.locations asm_result page_table
  in
  { arch = Litmus.Arch_id.to_string ir.arch;
    name = ir.name;
    threads;
    memory;
    kind = ir.kind;
    final =
      Assertion.map_cst (eval_term ~context:Final_assertion ~state) ir.assertion
  }
