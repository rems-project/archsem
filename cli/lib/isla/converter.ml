(** Orchestrate isla-to-Litmus.Testrepr.t conversion. *)

open Litmus

module RegValGen = Archsem.RegValGen

let regval_of_toml = function
  | Otoml.TomlInteger i -> RegValGen.Number (Z.of_int i)
  | Otoml.TomlInlineTable fields | Otoml.TomlTable fields ->
    RegValGen.Struct
      (List.map
        (fun (k, v) ->
          match v with
          | Otoml.TomlInteger i -> (k, RegValGen.Number (Z.of_int i))
          | _ -> failwith ("config: register field " ^ k ^ " must be integer"))
        fields)
  | _ -> failwith "config: register default must be integer or inline table"

let pc_reg arch =
  match arch with
  | Litmus.Arch_id.Arm -> Archsem.Arm.Reg.to_string Archsem.Arm.Reg.pc

let register_defaults () =
  let config = Config.get () in
  Otoml.find_or ~default:[] config (Otoml.get_table_values regval_of_toml)
    ["registers"; "defaults"]

let instruction_step () =
  let width =
    Otoml.find (Config.get ()) Otoml.get_integer ["assembler"; "instruction_step"]
  in
  if width <= 0 then failwith "config: [assembler] instruction_step must be positive";
  width

let default_memory_size () =
  let size =
    Otoml.find_or ~default:8 (Config.get ()) Otoml.get_integer ["isla"; "default_memory_size"] in
  if size <= 0 then failwith "config: [isla] default_memory_size must be positive";
  size

let reg_requirement op value =
  let value = RegValGen.Number value in
  match op with
  | Assertion.Eq -> Testrepr.ReqEq value
  | Assertion.Ne -> Testrepr.ReqNe value

let mem_requirement op value =
  match op with
  | Assertion.Eq -> Testrepr.MemEq value
  | Assertion.Ne -> Testrepr.MemNe value

(** Evaluate a term with page table context.
    Handles [pteN], [descN], [mkdescN], [s2mkdesc3] by dispatching to
    {!Pgtable} query helpers; other functions fall back to {!Term.eval_fn}. *)
let rec eval_pgt ~resolve ~table_data = function
  | Term.Const z -> z
  | Term.LocVal (Mem sym) -> Z.of_int (resolve sym)
  | Term.LocVal (Reg (tid, reg)) ->
    failwith (Printf.sprintf
      "term: cannot evaluate register reference %d:%s" tid reg)
  | Term.LocVal (Label name) ->
    failwith (Printf.sprintf
      "term: cannot evaluate label %s outside register init" name)
  | Term.Deref loc ->
    failwith (Printf.sprintf
      "term: cannot evaluate deref *%s" (Term.string_of_loc loc))
  | Term.Fn (name, args) ->
    let evaled = List.map (eval_pgt ~resolve ~table_data) args in
    eval_pgt_fn ~table_data name evaled
  | Term.KwFn (name, kw_args) ->
    let evaled =
      List.map (fun (k, v) -> (k, eval_pgt ~resolve ~table_data v)) kw_args in
    eval_pgt_kw_fn name evaled

and eval_pgt_fn ~table_data name args =
  let parse_level prefix name =
    let n = String.length prefix in
    if String.length name = n + 1 && String.sub name 0 n = prefix then
      Some (Char.code name.[n] - Char.code '0')
    else None
  in
  match parse_level "pte" name with
  | Some level ->
    (match args with
     | [va; base] ->
       Z.of_int (Function.lookup_pte_addr ~table_data
         ~base:(Z.to_int base) (Z.to_int va) level)
     | _ -> failwith (name ^ " requires 2 arguments: (va, base)"))
  | None ->
  match parse_level "desc" name with
  | Some level ->
    (match args with
     | [va; base] ->
       Z.of_int (Function.lookup_desc_value ~table_data
         ~base:(Z.to_int base) (Z.to_int va) level)
     | _ -> failwith (name ^ " requires 2 arguments: (va, base)"))
  | None ->
  if name = "asid" then
    (match args with
     | [v] -> Z.shift_left v 48
     | _ -> failwith "asid requires 1 argument")
  else
    Term.eval_fn name args

and eval_pgt_kw_fn name evaled_kw =
  let parse_mkdesc name =
    let prefix = "mkdesc" in
    let n = String.length prefix in
    if String.length name = n + 1 && String.sub name 0 n = prefix then
      Some (Char.code name.[n] - Char.code '0')
    else if name = "s2mkdesc3" then Some 3
    else None
  in
  match parse_mkdesc name with
  | Some level ->
    (match List.assoc_opt "table" evaled_kw with
     | Some table_addr ->
       Z.of_int (Function.table_descriptor (Z.to_int table_addr))
     | None ->
       let oa = match List.assoc_opt "oa" evaled_kw with
         | Some v -> Z.to_int v
         | None -> failwith (name ^ " requires oa= or table= argument")
       in
       let extra_bits = List.fold_left (fun acc (k, v) ->
         if k = "oa" then acc else acc lor Z.to_int v)
         0 evaled_kw in
       let attrs = Function.default_data_attrs lor extra_bits in
       Z.of_int (Function.make_desc ~level ~oa ~attrs))
  | None ->
    if name = "ttbr" then begin
      let base = match List.assoc_opt "base" evaled_kw with
        | Some v -> v
        | None -> failwith "ttbr requires base= argument"
      in
      let id_val =
        match List.assoc_opt "asid" evaled_kw, List.assoc_opt "vmid" evaled_kw with
        | Some v, _ | _, Some v -> v
        | None, None -> Z.zero
      in
      Z.logor (Z.shift_left id_val 48) base
    end else
      failwith (Printf.sprintf "term: unknown keyword function %s" name)

let resolve_term ~resolve ~table_data expr =
  match expr with
  | Term.LocVal loc -> `Loc loc
  | Term.Deref (Mem sym) -> `Deref sym
  | _ -> `Const (eval_pgt ~resolve ~table_data expr)

let atoms_to_conds ~resolve_sym ~va_pa_map ~table_data ~memory_size atoms =
  let resolve_ve expr =
    resolve_term ~resolve:resolve_sym ~table_data expr
  in
  let resolve_mem_addr sym =
    let va_addr = resolve_sym sym in
    match List.assoc_opt sym va_pa_map with
    | Some pa -> pa
    | None -> va_addr
  in
  let reg_atoms, mem_atoms =
    List.fold_left
      (fun (reg_atoms, mem_atoms) (Assertion.Cmp (lhs, op, rhs)) ->
        match resolve_ve lhs, resolve_ve rhs with
        | `Loc (Term.Reg (tid, reg)), `Const value ->
          ((tid, reg, reg_requirement op value) :: reg_atoms, mem_atoms)
        | `Loc (Term.Mem sym), `Const value ->
          let mem_cond : Testrepr.mem_cond =
            {
              sym;
              addr = resolve_mem_addr sym;
              size = memory_size sym;
              req = mem_requirement op value;
            }
          in
          (reg_atoms, mem_cond :: mem_atoms)
        | `Loc (Term.Reg _), `Loc _ ->
          failwith "assertion: register-to-location comparisons are not supported"
        | `Loc (Term.Mem _), _ ->
          failwith "assertion: memory-to-location comparisons are not supported"
        | `Loc (Term.Label _), _ | _, `Loc (Term.Label _) ->
          failwith "assertion: labels in assertions are not supported"
        | _, `Deref _ ->
          failwith "assertion: deref (*x) on RHS is not supported"
        | `Deref sym, `Const value ->
          let mem_cond =
            {
              Testrepr.sym = sym;
              addr = resolve_mem_addr sym;
              size = memory_size sym;
              req = mem_requirement op value;
            }
          in
          (reg_atoms, mem_cond :: mem_atoms)
        | `Deref _, _ ->
          failwith "assertion: deref (*x) on LHS requires constant RHS"
        | `Const _, _ ->
          failwith "assertion: constant expression on LHS is not supported")
      ([], [])
      atoms
  in
  let reg_atoms = List.rev reg_atoms
  and mem_atoms = List.rev mem_atoms in
  let tids = List.sort_uniq compare (List.map (fun (tid, _, _) -> tid) reg_atoms) in
  let thread_conds =
    List.map
      (fun tid ->
        let reqs =
          List.filter_map
            (fun (tid', reg, req) -> if tid' = tid then Some (reg, req) else None)
            reg_atoms
        in
        (tid, reqs))
      tids
  in
  (thread_conds, mem_atoms)

let to_final_conds ~expect_is_sat ~resolve_sym ~va_pa_map ~table_data ~memory_size assertion =
  let is_observable, dnf =
    match assertion with
    | Assertion.Not e -> (not expect_is_sat, Assertion.to_dnf e)
    | e -> (expect_is_sat, Assertion.to_dnf e)
  in
  List.filter_map
    (fun conj ->
      if conj = [] then
        None
      else
        let thread_conds, mem_conds =
          atoms_to_conds ~resolve_sym ~va_pa_map ~table_data ~memory_size conj
        in
        if is_observable then
          Some (Testrepr.Observable (thread_conds, mem_conds))
        else
          Some (Testrepr.Unobservable (thread_conds, mem_conds)))
    dnf

let z_of_value ~resolve ~table_data expr =
  eval_pgt ~resolve ~table_data expr

let build_registers ~resolve ~table_data ~label_env ~arch pc (thread : Ir.thread) =
  let pc_entry = (pc_reg arch, RegValGen.Number (Z.of_int pc)) in
  let used_regs =
    List.map
      (fun (reg, value) ->
        match value with
        | Term.LocVal (Label name) ->
          let addr = match List.assoc_opt name label_env with
            | Some a -> a
            | None -> failwith ("converter: unresolved label " ^ name)
          in
          (reg, RegValGen.Number (Z.of_int addr))
        | _ ->
          (reg, RegValGen.Number (z_of_value ~resolve ~table_data value)))
      thread.init
  in
  let has name = List.exists (fun (reg, _) -> reg = name) used_regs in
  let default_regs =
    List.filter_map (fun (reg, value) ->
      if has reg then None else Some (reg, value)) (register_defaults ())
  in
  pc_entry :: used_regs @ default_regs

let build_code_memory ~step addr data =
  {
    Testrepr.addr;
    step;
    data;
    sym = None;
    kind = Testrepr.Code;
  }

let build_data_memory ~resolve ~table_data sym addr init_value =
  let mem_size = default_memory_size () in
  let value = z_of_value ~resolve ~table_data init_value in
  if Z.numbits value > (mem_size * 8) then
    failwith ("Number doesn't fit in symbol " ^ sym);
  let data = Bytes.make mem_size '\x00' in
  let bits = Z.to_bits value in
  Bytes.blit_string bits 0 data 0 (min mem_size (String.length bits));
  {
    Testrepr.addr = addr;
    step = mem_size;
    data;
    sym = Some sym;
    kind = Testrepr.Data;
  }

let to_testrepr (ir : Ir.t) : Testrepr.t =
  let syms = Symbols.empty () in
  (* Evaluate page table setup DSL *)
  let _syms, pgt_memory, _walks, pgt_mem_inits, l0_addr, va_pa_map, pgt_addrs =
    Pgtable.evaluate ~arch:ir.arch ~symbolic:ir.symbolic syms
      ir.page_table_setup
  in
  (* Collect all data symbols: ir.symbolic + pgt-declared virtual/physical names *)
  let all_data_syms =
    let from_pgt =
      List.filter_map (fun (name, _) ->
        if List.mem name ir.symbolic then None else Some name)
        pgt_addrs
    in
    ir.symbolic @ from_pgt
  in
  (* Ensure all data symbols are allocated *)
  List.iter (fun name -> ignore (Symbols.alloc_data syms name)) all_data_syms;
  let assembled_threads =
    List.map
      (fun (thread : Ir.thread) ->
        let enc, labels = Assembler.assemble thread.code in
        let code_addr = Symbols.alloc_page syms in
        let label_env =
          List.map (fun (name, off) -> (name, code_addr + off)) labels in
        (thread, enc, code_addr, label_env))
      ir.threads
  in
  let code_step = instruction_step () in
  let resolve = Symbols.resolve syms in
  let table_data =
    List.map (fun (b : Testrepr.memory_block) -> (b.addr, b.data)) pgt_memory
  in
  (* Auto-add identity mappings for code pages when page tables are present *)
  (match l0_addr with
   | Some base ->
     List.iter (fun (_, _, code_addr, _) ->
       Pgtable.add_identity_code_entry ~table_data ~base code_addr)
       assembled_threads
   | None -> ());
  let pgt_auto_regs = match l0_addr with
    | Some l0 -> [("TTBR0_EL1", RegValGen.Number (Z.of_int l0))]
    | None -> []
  in
  let registers =
    List.map
      (fun (thread, _, code_addr, label_env) ->
        let regs =
          build_registers ~resolve ~table_data ~label_env ~arch:ir.arch code_addr thread in
        let has name = List.exists (fun (k, _) -> k = name) regs in
        regs @ List.filter (fun (k, _) -> not (has k)) pgt_auto_regs)
      assembled_threads
  in
  let code_memory =
    List.map
      (fun (_, enc, code_addr, _) -> build_code_memory ~step:code_step code_addr enc)
      assembled_threads
  in
  (* Merge page table mem inits: DSL overrides ir.locations *)
  let locations =
    let pgt_locs = List.rev pgt_mem_inits in
    let overridden name = List.exists (fun (k, _) -> k = name) pgt_locs in
    List.filter (fun (k, _) -> not (overridden k)) ir.locations @ pgt_locs
  in
  let data_memory =
    let seen_addrs = Hashtbl.create 16 in
    List.filter_map (fun sym ->
      let va_addr = Symbols.resolve syms sym in
      let addr = match List.assoc_opt sym va_pa_map with
        | Some pa -> pa
        | None -> va_addr
      in
      if Hashtbl.mem seen_addrs addr then None
      else begin
        Hashtbl.replace seen_addrs addr true;
        let init_value =
          List.assoc_opt sym locations |> Option.value ~default:(Term.Const Z.zero)
        in
        Some (build_data_memory ~resolve ~table_data sym addr init_value)
      end)
    all_data_syms
  in
  let mem_sizes =
    List.filter_map
      (fun (block : Testrepr.memory_block) ->
        Option.map (fun sym -> (sym, block.step)) block.sym)
      data_memory
  in
  let memory_size sym =
    match List.assoc_opt sym mem_sizes with
    | Some size -> size
    | None -> failwith ("isla: unknown memory size for symbol: " ^ sym)
  in
  let term_cond =
    let pc = pc_reg ir.arch in
    List.map
      (fun (_, enc, code_addr, _) ->
        let end_pc = Z.of_int (code_addr + Bytes.length enc) in
        [(pc, RegValGen.Number end_pc)])
      assembled_threads
  in
  let finals =
    to_final_conds
      ~expect_is_sat:(ir.expect = Ir.Sat)
      ~resolve_sym:(Symbols.resolve syms)
      ~va_pa_map
      ~table_data
      ~memory_size
      ir.assertion
  in
  {
    arch = Litmus.Arch_id.to_string ir.arch;
    name = ir.name;
    registers;
    memory = code_memory @ Pgtable.to_sparse_blocks table_data @ data_memory;
    term_cond;
    finals;
  }
