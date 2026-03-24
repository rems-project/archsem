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
    Otoml.find_or ~default:8 (Config.get ()) Otoml.get_integer
      ["isla"; "default_memory_size"]
  in
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

let atoms_to_conds ~resolve_sym ~memory_size atoms =
  let (reg_atoms, mem_atoms) =
    List.fold_left
      (fun (reg_atoms, mem_atoms) atom ->
         match atom with
         | Assertion.CmpCst (Assertion.Reg (tid, reg), op, value) ->
             ((tid, reg, reg_requirement op value) :: reg_atoms, mem_atoms)
         | Assertion.CmpCst (Assertion.Mem sym, op, value) ->
             let mem_cond : Testrepr.mem_cond =
               { sym;
                 addr = resolve_sym sym;
                 size = memory_size sym;
                 req = mem_requirement op value
               }
             in
             (reg_atoms, mem_cond :: mem_atoms)
         | Assertion.CmpLoc (Assertion.Reg _, _, _) ->
             failwith
               "assertion: register-to-location comparisons are not supported"
         | Assertion.CmpLoc (Assertion.Mem _, _, _) ->
             failwith
               "assertion: memory-to-location comparisons are not supported"
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

let to_final_conds ~expect_is_sat ~resolve_sym ~memory_size assertion =
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

let z_of_value syms = function
  | Ir.Int z -> z
  | Ir.Sym sym -> Z.of_int (Symbols.resolve syms sym)

let build_registers syms ~arch pc (thread : Ir.thread) =
  let pc_entry = (pc_reg arch, RegValGen.Number (Z.of_int pc)) in
  let used_regs =
    List.map
      (fun (reg, value) -> (reg, RegValGen.Number (z_of_value syms value)))
      thread.init
  in
  let has name = List.exists (fun (reg, _) -> reg = name) used_regs in
  let default_regs =
    List.filter_map
      (fun (reg, value) -> if has reg then None else Some (reg, value))
      (register_defaults ())
  in
  (pc_entry :: used_regs) @ default_regs

let build_code_memory ~step addr data =
  {Testrepr.addr; step; data; sym = None; kind = Testrepr.Code}

let build_data_memory syms sym addr init_value =
  let mem_size = default_memory_size () in
  let value = z_of_value syms init_value in
  if Z.numbits value > mem_size * 8 then
    failwith ("Number doesn't fit in symbol " ^ sym);
  let data = Bytes.make mem_size '\x00' in
  let bits = Z.to_bits value in
  Bytes.blit_string bits 0 data 0 (min mem_size (String.length bits));
  {Testrepr.addr; step = mem_size; data; sym = Some sym; kind = Testrepr.Data}

let to_testrepr (ir : Ir.t) : Testrepr.t =
  let syms = Symbols.empty () in
  List.iter (Symbols.alloc_sym syms) ir.symbolic;
  let encoded_threads =
    List.map
      (fun (thread : Ir.thread) ->
         let enc = Assembler.assemble thread.code in
         let code_addr = Symbols.alloc_page syms in
         (thread, enc, code_addr)
       )
      ir.threads
  in
  let code_step = instruction_step () in
  let registers =
    List.map
      (fun (thread, _, code_addr) ->
         build_registers syms ~arch:ir.arch code_addr thread
       )
      encoded_threads
  in
  let code_memory =
    List.map
      (fun (_, enc, code_addr) -> build_code_memory ~step:code_step code_addr enc)
      encoded_threads
  in
  let data_memory =
    List.map
      (fun sym ->
         let addr = Symbols.resolve syms sym in
         let init_value =
           List.assoc_opt sym ir.locations |> Option.value ~default:(Ir.Int Z.zero)
         in
         build_data_memory syms sym addr init_value
       )
      ir.symbolic
  in
  let mem_sizes =
    List.filter_map
      (fun (block : Testrepr.memory_block) ->
         Option.map (fun sym -> (sym, Testrepr.block_size block)) block.sym
       )
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
      (fun (_, enc, code_addr) ->
         let end_pc = Z.of_int (code_addr + Bytes.length enc) in
         [(pc, RegValGen.Number end_pc)]
       )
      encoded_threads
  in
  let finals =
    to_final_conds ~expect_is_sat:(ir.expect = Ir.Sat)
      ~resolve_sym:(Symbols.resolve syms) ~memory_size ir.assertion
  in
  { arch = Litmus.Arch_id.to_string ir.arch;
    name = ir.name;
    registers;
    memory = code_memory @ data_memory;
    term_cond;
    finals
  }
