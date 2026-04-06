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

    Two paths depending on whether page tables are present:
    - Non-VM: Assembler handles code + data layout via ELF pipeline
    - VM: Assembler handles code layout; Pgtable handles data + page tables *)

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

(* {1 Assertion / final condition helpers} *)

let reg_requirement op value =
  let value = RegValGen.Number value in
  match op with
  | Assertion.Eq -> Testrepr.ReqEq value
  | Assertion.Ne -> Testrepr.ReqNe value

let mem_requirement op value =
  match op with
  | Assertion.Eq -> Testrepr.MemEq value
  | Assertion.Ne -> Testrepr.MemNe value

(* {1 Term evaluation with symbol resolution} *)

(** Build an evaluation environment from a symbol resolver. *)
let make_env resolve = function
  | Term.Mem sym -> Some (Z.of_int (resolve sym))
  | Term.Reg _ -> None

(** Evaluate a term, resolving symbols via [resolve] and using [table_data]
    for page table query functions (pteN, descN, etc. registered in Function). *)
let eval_term ~resolve ~table_data expr =
  Term.eval ~td:table_data ~env:(make_env resolve) expr

(** Evaluate a keyword function call that isn't in the standard Function registry.
    Handles [mkdescN] with extra attribute keywords and [ttbr] with asid/vmid. *)
let eval_converter_kwfn ~resolve ~table_data name kw_args =
  let eval_kw =
    List.map (fun (k, v) -> (k, eval_term ~resolve ~table_data v)) kw_args
  in
  let parse_mkdesc name =
    let prefix = "mkdesc" in
    let n = String.length prefix in
    if String.length name = n + 1 && String.sub name 0 n = prefix then
      Some (Char.code name.[n] - Char.code '0')
    else if name = "s2mkdesc3" then Some 3
    else None
  in
  match parse_mkdesc name with
  | Some _level -> (
    match List.assoc_opt "table" eval_kw with
    | Some table_addr ->
        Z.of_int (Pgtable_desc.table_descriptor (Z.to_int table_addr))
    | None ->
        let oa =
          match List.assoc_opt "oa" eval_kw with
          | Some v -> Z.to_int v
          | None -> failwith (name ^ " requires oa= or table= argument")
        in
        let extra_bits =
          List.fold_left
            (fun acc (k, v) -> if k = "oa" then acc else acc lor Z.to_int v)
            0 eval_kw
        in
        let attrs = Pgtable_desc.aarch64_data_attrs lor extra_bits in
        Z.of_int (Pgtable_desc.make_desc ~level:3 ~oa ~attrs ())
  )
  | None ->
      if name = "ttbr" then begin
        let base =
          match List.assoc_opt "base" eval_kw with
          | Some v -> v
          | None -> failwith "ttbr requires base= argument"
        in
        let id_val =
          match
            (List.assoc_opt "asid" eval_kw, List.assoc_opt "vmid" eval_kw)
          with
          | (Some v, _) | (_, Some v) -> v
          | (None, None) -> Z.zero
        in
        Z.logor (Z.shift_left id_val 48) base
      end
      else
        (* Fall back to standard kwfn evaluation *)
        Term.eval ~td:table_data ~env:(make_env resolve)
          (Term.KwFn (name, kw_args))

(** Evaluate a term, with converter-specific keyword function handling. *)
let eval_value ~resolve ~table_data = function
  | Term.KwFn (name, kw_args) ->
      eval_converter_kwfn ~resolve ~table_data name kw_args
  | expr -> eval_term ~resolve ~table_data expr

(* {1 Shared final condition building} *)

let resolve_term ~resolve ~table_data expr =
  match expr with
  | Term.LocVal loc -> `Loc loc
  | Term.Deref (Mem sym) -> `Deref sym
  | _ -> `Const (eval_value ~resolve ~table_data expr)

let atoms_to_conds ~resolve_sym ~va_pa_map ~table_data ~memory_size atoms =
  let resolve_ve expr = resolve_term ~resolve:resolve_sym ~table_data expr in
  let resolve_mem_addr sym =
    let va_addr = resolve_sym sym in
    match List.assoc_opt sym va_pa_map with Some pa -> pa | None -> va_addr
  in
  let (reg_atoms, mem_atoms) =
    List.fold_left
      (fun (reg_atoms, mem_atoms) (Assertion.Cmp (lhs, op, rhs)) ->
         match (resolve_ve lhs, resolve_ve rhs) with
         | (`Loc (Term.Reg (tid, reg)), `Const value) ->
             ((tid, reg, reg_requirement op value) :: reg_atoms, mem_atoms)
         | (`Loc (Term.Mem sym), `Const value) ->
             let mc : Testrepr.mem_cond =
               { sym;
                 addr = resolve_mem_addr sym;
                 size = memory_size sym;
                 req = mem_requirement op value
               }
             in
             (reg_atoms, mc :: mem_atoms)
         | (`Deref sym, `Const value) ->
             let mc : Testrepr.mem_cond =
               { sym;
                 addr = resolve_sym sym;
                 size = memory_size sym;
                 req = mem_requirement op value
               }
             in
             (reg_atoms, mc :: mem_atoms)
         | (`Loc (Term.Reg _), `Loc _) ->
             failwith "assertion: register-to-location comparisons not supported"
         | (`Loc (Term.Mem _), _) ->
             failwith "assertion: memory-to-location comparisons not supported"
         | (_, `Deref _) -> failwith "assertion: deref (*x) on RHS not supported"
         | (`Deref _, _) ->
             failwith "assertion: deref (*x) on LHS requires constant RHS"
         | (`Const _, _) -> failwith "assertion: constant on LHS not supported"
       )
      ([], []) atoms
  in
  let reg_atoms = List.rev reg_atoms and mem_atoms = List.rev mem_atoms in
  let tids =
    List.sort_uniq compare (List.map (fun (tid, _, _) -> tid) reg_atoms)
  in
  let thread_conds =
    List.map
      (fun tid ->
         let reqs =
           List.filter_map
             (fun (tid', reg, req) -> if tid' = tid then Some (reg, req) else None)
             reg_atoms
         in
         (tid, reqs)
       )
      tids
  in
  (thread_conds, mem_atoms)

let build_finals
      ~expect_is_sat
      ~resolve_sym
      ~va_pa_map
      ~table_data
      ~memory_size
      assertion
  =
  let (is_observable, dnf) =
    match assertion with
    | Assertion.Not e -> (not expect_is_sat, Assertion.to_dnf e)
    | e -> (expect_is_sat, Assertion.to_dnf e)
  in
  List.filter_map
    (fun conj ->
       if conj = [] then None
       else
         let (tc, mc) =
           atoms_to_conds ~resolve_sym ~va_pa_map ~table_data ~memory_size conj
         in
         if is_observable then Some (Testrepr.Observable (tc, mc))
         else Some (Testrepr.Unobservable (tc, mc))
     )
    dnf

(* {1 Non-VM path: Assembler handles everything} *)

let init_bytes_of_z mem_size sym value =
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
         {Assembler.name = sym; init_bytes = init_bytes_of_z mem_size sym value}
       )
      ir.symbolic
  in
  {sections = code_sections @ fixed_sections; symbols = data_symbols}

let find_section name (asm_result : Assembler.assembly_result) =
  List.find
    (fun (s : Assembler.linked_section) -> s.name = name)
    asm_result.sections

(** Build code memory blocks from assembled sections. *)
let build_code_memory asm_result =
  let code_step = instruction_step () in
  List.map
    (fun (sec : Assembler.linked_section) ->
       { Testrepr.addr = sec.addr;
         step = code_step;
         data = sec.data;
         sym = None;
         kind = Testrepr.Code
       }
     )
    asm_result.Assembler.sections

(** Build per-thread termination conditions (PC at end of code). *)
let build_term_cond ~arch asm_result threads =
  let pc = pc_reg arch in
  List.mapi
    (fun i _thread ->
       let sec = find_section (Printf.sprintf "thread%d" i) asm_result in
       let end_pc = Z.of_int (sec.addr + Bytes.length sec.data) in
       [(pc, RegValGen.Number end_pc)]
     )
    threads

(** Build per-thread register maps: PC + user init + config defaults. *)
let build_registers ~arch ~eval_init ~extra_regs asm_result threads =
  List.mapi
    (fun i (thread : Ir.thread) ->
       let sec = find_section (Printf.sprintf "thread%d" i) asm_result in
       let pc_entry = (pc_reg arch, RegValGen.Number (Z.of_int sec.addr)) in
       let used_regs =
         List.map
           (fun (reg, value) -> (reg, RegValGen.Number (eval_init value)))
           thread.init
       in
       let has name = List.exists (fun (r, _) -> r = name) used_regs in
       let defaults =
         List.filter_map
           (fun (r, v) -> if has r then None else Some (r, v))
           (register_defaults ())
       in
       let regs = (pc_entry :: used_regs) @ defaults in
       regs @ List.filter (fun (k, _) -> not (has k)) extra_regs
     )
    threads

let to_testrepr_simple (ir : Ir.t) : Testrepr.t =
  let asm_input = to_assembly_input ir in
  let asm_result = Assembler.assemble asm_input in
  let data_symbols = asm_input.symbols in
  let resolve sym = Assembler.resolve_symbol asm_result sym in
  let mem_size = default_memory_size () in
  let registers =
    build_registers ~arch:ir.arch
      ~eval_init:(eval_term ~resolve ~table_data:[])
      ~extra_regs:[] asm_result ir.threads
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
  let memory_size sym =
    match
      List.find_opt (fun (s : Assembler.data_symbol) -> s.name = sym) data_symbols
    with
    | Some s -> Bytes.length s.init_bytes
    | None -> Error.fatal "unknown memory size for: %s" sym
  in
  let finals =
    build_finals ~expect_is_sat:(ir.expect = Ir.Sat) ~resolve_sym:resolve
      ~va_pa_map:[] ~table_data:[] ~memory_size ir.assertion
  in
  { arch = Litmus.Arch_id.to_string ir.arch;
    name = ir.name;
    registers;
    memory = build_code_memory asm_result @ data_memory;
    term_cond = build_term_cond ~arch:ir.arch asm_result ir.threads;
    finals
  }

(* {1 VM path: Assembler for code, Pgtable for data + tables} *)

(** Assemble only code (threads + fixed sections), no data symbols. *)
let assemble_code_only (ir : Ir.t) : Assembler.assembly_result =
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
  Assembler.assemble {sections = code_sections @ fixed_sections; symbols = []}

let to_testrepr_vm (ir : Ir.t) : Testrepr.t =
  (* Step 1: Assemble code via ELF pipeline *)
  let asm_result = assemble_code_only ir in
  (* Step 2: Evaluate page table DSL (allocates PA/VA/tables internally) *)
  let (pgt_memory, _walks, pgt_mem_inits, l0_addr, va_pa_map, pgt_addrs) =
    Pgtable.evaluate ~arch:ir.arch ~symbolic:ir.symbolic ir.page_table_setup
  in
  let pgt_resolve name =
    match List.assoc_opt name pgt_addrs with
    | Some addr -> addr
    | None -> failwith ("pgtable: unresolved symbol: " ^ name)
  in
  let table_data =
    List.map (fun (b : Testrepr.memory_block) -> (b.addr, b.data)) pgt_memory
  in
  (* Step 3: Auto-add identity mappings for code pages *)
  ( match l0_addr with
  | Some base ->
      List.iter
        (fun (sec : Assembler.linked_section) ->
           Pgtable.add_identity_code_entry ~table_data ~base sec.addr
         )
        asm_result.sections
  | None -> ()
  );
  let mem_size = default_memory_size () in
  (* Step 4: Build registers *)
  let pgt_auto_regs =
    match l0_addr with
    | Some l0 -> [("TTBR0_EL1", RegValGen.Number (Z.of_int l0))]
    | None -> []
  in
  let registers =
    build_registers ~arch:ir.arch
      ~eval_init:(eval_value ~resolve:pgt_resolve ~table_data)
      ~extra_regs:pgt_auto_regs asm_result ir.threads
  in
  (* Step 5: Build memory *)
  (* Merge page table mem inits: DSL overrides ir.locations *)
  let locations =
    let pgt_locs = List.rev pgt_mem_inits in
    let overridden name = List.exists (fun (k, _) -> k = name) pgt_locs in
    List.filter (fun (k, _) -> not (overridden k)) ir.locations @ pgt_locs
  in
  let data_memory =
    let seen_addrs = Hashtbl.create 16 in
    List.filter_map
      (fun sym ->
         let va_addr = pgt_resolve sym in
         let addr =
           match List.assoc_opt sym va_pa_map with
           | Some pa -> pa
           | None -> va_addr
         in
         if Hashtbl.mem seen_addrs addr then None
         else begin
           Hashtbl.replace seen_addrs addr true;
           let init_value =
             List.assoc_opt sym locations
             |> Option.value ~default:(Term.Const Z.zero)
           in
           let z = eval_value ~resolve:pgt_resolve ~table_data init_value in
           let data = init_bytes_of_z mem_size sym z in
           Some
             { Testrepr.addr;
               step = mem_size;
               data;
               sym = Some sym;
               kind = Testrepr.Data
             }
         end
       )
      ir.symbolic
  in
  (* Step 6: Termination + finals *)
  let mem_sizes =
    List.filter_map
      (fun (b : Testrepr.memory_block) ->
         Option.map (fun sym -> (sym, b.step)) b.sym
       )
      data_memory
  in
  let memory_size sym =
    match List.assoc_opt sym mem_sizes with
    | Some size -> size
    | None -> failwith ("unknown memory size for: " ^ sym)
  in
  let finals =
    build_finals ~expect_is_sat:(ir.expect = Ir.Sat) ~resolve_sym:pgt_resolve
      ~va_pa_map ~table_data ~memory_size ir.assertion
  in
  { arch = Litmus.Arch_id.to_string ir.arch;
    name = ir.name;
    registers;
    memory =
      build_code_memory asm_result
      @ Pgtable.to_sparse_blocks table_data
      @ data_memory;
    term_cond = build_term_cond ~arch:ir.arch asm_result ir.threads;
    finals
  }

(* {1 Entry point} *)

let to_testrepr (ir : Ir.t) : Testrepr.t =
  if ir.page_table_setup = [] then to_testrepr_simple ir else to_testrepr_vm ir
