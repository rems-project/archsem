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

(* {1 Config helpers} *)

let regval_of_toml = function
  | Otoml.TomlInteger i -> RegValGen.Number (Z.of_int i)
  | Otoml.TomlInlineTable fields | Otoml.TomlTable fields ->
      RegValGen.Struct
        (List.map
           (fun (k, v) ->
              match v with
              | Otoml.TomlInteger i -> (k, RegValGen.Number (Z.of_int i))
              | _ -> failwith ("config: register field " ^ k ^ " must be integer")
            )
           fields
        )
  | _ -> failwith "config: register default must be integer or inline table"

let pc_reg arch =
  match arch with
  | Litmus.Arch_id.Arm -> Archsem.Arm.Reg.to_string Archsem.Arm.Reg.pc
  | Litmus.Arch_id.X86 -> Archsem.X86.Reg.to_string Archsem.X86.Reg.pc

let register_defaults () =
  let config = Config.get () in
  Otoml.find_or ~default:[] config
    (Otoml.get_table_values regval_of_toml)
    ["registers"; "defaults"]

let instruction_step () =
  let width =
    Otoml.find (Config.get ()) Otoml.get_integer ["assembler"; "instruction_step"]
  in
  if width <= 0 then
    failwith "config: [assembler] instruction_step must be positive";
  width

let default_memory_size () =
  let size =
    Otoml.find (Config.get ()) Otoml.get_integer ["isla"; "default_memory_size"]
  in
  if size <= 0 then failwith "config: [isla] default_memory_size must be positive";
  size

(* {1 IR to assembly_input} *)

let z_of_value asm_result expr =
  let env = function
    | Term.Mem sym -> Some (Z.of_int (Assembler.resolve_symbol asm_result sym))
    | _ -> None
  in
  Term.eval ~env expr

let init_bytes_of_value mem_size sym value =
  if Z.numbits value > mem_size * 8 then
    Error.fatal "Number doesn't fit in symbol %s" sym;
  let data = Bytes.make mem_size '\x00' in
  let bits = Z.to_bits value in
  Bytes.blit_string bits 0 data 0 (min mem_size (String.length bits));
  data

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
           List.assoc_opt sym ir.locations
           |> Option.value ~default:(Term.Const Z.zero)
         in
         let value =
           match init_value with
           | Term.Const z -> z
           | _ ->
               Error.fatal
                 "non-constant location initializer not supported before linking"
         in
         { Assembler.name = sym;
           init_bytes = init_bytes_of_value mem_size sym value
         }
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

(* {1 Memory, registers, and termination} *)

(** Convert linked sections and data symbols into Testrepr memory blocks. *)
let build_memory ~data_symbols (asm_result : Assembler.assembly_result) =
  let code_step = instruction_step () in
  let mem_size = default_memory_size () in
  let code_memory =
    List.map
      (fun (sec : Assembler.linked_section) ->
         { Testrepr.addr = sec.addr;
           step = code_step;
           data = sec.data;
           sym = None;
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
let build_registers
      ~arch
      (asm_result : Assembler.assembly_result)
      (threads : Ir.thread list)
  =
  List.mapi
    (fun i (thread : Ir.thread) ->
       let sec = find_section (Printf.sprintf "thread%d" i) asm_result in
       let pc_entry = (pc_reg arch, RegValGen.Number (Z.of_int sec.addr)) in
       let used_regs =
         List.map
           (fun (reg, value) ->
              (reg, RegValGen.Number (z_of_value asm_result value))
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
     )
    threads

(** Build per-thread termination conditions (PC at end of code).
    TODO: support additional conditions (e.g. exceptions, watchpoints). *)
let build_term_cond
      ~arch
      (asm_result : Assembler.assembly_result)
      (threads : Ir.thread list)
  =
  let pc = pc_reg arch in
  List.mapi
    (fun i _thread ->
       let sec = find_section (Printf.sprintf "thread%d" i) asm_result in
       let end_pc = Z.of_int (sec.addr + Bytes.length sec.data) in
       [(pc, RegValGen.Number end_pc)]
     )
    threads

(* {1 Final conditions} *)

let reg_requirement op value =
  let value = RegValGen.Number value in
  match op with
  | Assertion.Eq -> Testrepr.ReqEq value
  | Assertion.Ne -> Testrepr.ReqNe value

let mem_requirement op value =
  match op with
  | Assertion.Eq -> Testrepr.MemEq value
  | Assertion.Ne -> Testrepr.MemNe value

(** Resolve a Term.t to location, deref, or constant. *)
let resolve_term = function
  | Term.LocVal loc -> `Loc loc
  | Term.Deref (Term.Mem sym) -> `Deref sym
  | Term.Const z -> `Const z
  | _ -> failwith "assertion: unsupported term form"

(** Convert a single assertion atom into a register or memory condition. *)
let atom_to_cond ~resolve_sym ~memory_size (Assertion.Cmp (lhs, op, rhs)) =
  match (resolve_term lhs, resolve_term rhs) with
  | (`Loc (Term.Reg (tid, reg)), `Const z) -> `Reg (tid, reg, reg_requirement op z)
  | (`Deref sym, `Const z) ->
      `Mem
        ( { Testrepr.sym;
            addr = resolve_sym sym;
            size = memory_size sym;
            req = mem_requirement op z
          }
         : Testrepr.mem_cond
         )
  | (`Loc (Term.Mem _), _) ->
      Error.fatal "assertion: bare memory symbol not supported, use *sym"
  | _ -> Error.fatal "assertion: unsupported comparison form"

(** Partition atoms into per-thread register conditions and memory conditions. *)
let atoms_to_conds ~resolve_sym ~memory_size atoms =
  let (reg_conds, mem_conds) =
    List.partition_map
      (fun atom ->
         match atom_to_cond ~resolve_sym ~memory_size atom with
         | `Reg (t, r, req) -> Left (t, r, req)
         | `Mem m -> Right m
       )
      atoms
  in
  let thread_conds =
    let sorted =
      List.sort
        (fun (t1, r1, _) (t2, r2, _) -> compare (t1, r1) (t2, r2))
        reg_conds
    in
    List.fold_left
      (fun acc (tid, reg, req) ->
         match acc with
         | (tid', reqs) :: rest when tid' = tid ->
             (tid', reqs @ [(reg, req)]) :: rest
         | _ -> (tid, [(reg, req)]) :: acc
       )
      [] sorted
    |> List.rev
  in
  (thread_conds, mem_conds)

let build_finals ~expect_is_sat ~resolve_sym ~memory_size assertion =
  let (is_observable, dnf) =
    match assertion with
    | Assertion.Not e -> (not expect_is_sat, Assertion.to_dnf e)
    | e -> (expect_is_sat, Assertion.to_dnf e)
  in
  List.filter_map
    (fun conj ->
       if conj = [] then None
       else
         let (thread_conds, mem_conds) =
           atoms_to_conds ~resolve_sym ~memory_size conj
         in
         if is_observable then Some (Testrepr.Observable (thread_conds, mem_conds))
         else Some (Testrepr.Unobservable (thread_conds, mem_conds))
     )
    dnf

(* {1 Orchestration} *)

let to_testrepr (ir : Ir.t) : Testrepr.t =
  let asm_input = to_assembly_input ir in
  let asm_result = Assembler.assemble asm_input in
  let data_symbols = asm_input.symbols in
  let resolve sym = Assembler.resolve_symbol asm_result sym in
  let registers = build_registers ~arch:ir.arch asm_result ir.threads in
  let memory = build_memory ~data_symbols asm_result in
  let term_cond = build_term_cond ~arch:ir.arch asm_result ir.threads in
  let memory_size sym =
    match
      List.find_opt (fun (s : Assembler.data_symbol) -> s.name = sym) data_symbols
    with
    | Some s -> Bytes.length s.init_bytes
    | None -> Error.fatal "unknown memory size for: %s" sym
  in
  let finals =
    build_finals ~expect_is_sat:(ir.expect = Ir.Sat) ~resolve_sym:resolve
      ~memory_size ir.assertion
  in
  { arch = Litmus.Arch_id.to_string ir.arch;
    name = ir.name;
    registers;
    memory;
    term_cond;
    finals
  }
