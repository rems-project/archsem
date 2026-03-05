(** Orchestrate isla-to-Litmus.Spec.t conversion.

    Pipeline:
    1. Parse isla TOML -> Input.t
    2. Allocate symbols -> Symbols.t
    3. Encode assembly -> Assembler.encoded per thread
    4. Parse assertions -> Spec.final_cond list
    5. Build Litmus.Spec.t *)

open Archsem
open Litmus

let reg_of_name name =
  match Reg.of_string name with
  | Some r -> r
  | None -> failwith ("converter: unrecognized register name: " ^ name)

let default_sys_regs = [("SCTLR_EL1", Z.zero)]

let default_pstate =
  RegVal.Struct [("EL", RegVal.Number Z.zero); ("SP", RegVal.Number Z.zero)]

let resolve_init_value syms value =
  match Symbols.resolve syms value with
  | Some addr -> RegVal.Number addr
  | None ->
    try RegVal.Number (Z.of_string value)
    with Invalid_argument _ -> RegVal.String value

let build_registers syms pc (thread : Input.thread) =
  let user_regs = List.map (fun (reg, value) ->
    (reg_of_name (Assertion.normalize_reg reg), resolve_init_value syms value)
  ) thread.init in
  let has name = List.exists (fun (r, _) -> r = reg_of_name name) user_regs in
  let pc_entry = (Reg.pc, RegVal.Number pc) in
  let gp_regs = List.init 31 (fun i ->
    let r = Reg.r i in
    if List.exists (fun (r', _) -> r = r') user_regs then None
    else Some (r, RegVal.Number Z.zero)
  ) |> List.filter_map Fun.id in
  let sys_regs = List.filter_map (fun (r, v) ->
    if has r then None else Some (reg_of_name r, RegVal.Number v)) default_sys_regs in
  let pstate = if has "PSTATE" then [] else [(Reg.pstate, default_pstate)] in
  pc_entry :: user_regs @ gp_regs @ sys_regs @ pstate

let write_le buf offset step v =
  for j = 0 to step - 1 do
    Bytes.set buf (offset + j) (Char.chr ((v lsr (j * 8)) land 0xFF))
  done

let build_code_memory base (enc : Assembler.encoded) =
  let total_size = List.fold_left (+) 0 enc.widths in
  let step = match enc.widths with w :: _ -> w | [] -> 4 in
  let data = Bytes.create total_size in
  let _ = List.fold_left2 (fun offset word width ->
    write_le data offset width word; offset + width
  ) 0 enc.bytes enc.widths in
  { Spec.
    base;
    size = total_size;
    step;
    data;
    name = None;
    kind = Some Spec.Code;
  }

let build_data_memory name addr init_value =
  let mem_size = Config.default_mem_size () in
  let v = Z.to_int (Z.of_string init_value) in
  let data = Bytes.create mem_size in
  write_le data 0 mem_size v;
  { Spec.
    base = addr;
    size = mem_size;
    step = mem_size;
    data;
    name = Some name;
    kind = Some Spec.Data;
  }

let to_spec (input : Input.t) =
  let cfg = Config.get () in
  let command = match Config.get_string_opt ["assembler"; "command"] cfg with
    | Some cmd -> cmd
    | None -> failwith "config: [assembler] command is required"
  in

  (* 1. Allocate symbols *)
  let syms = List.fold_left (fun syms name ->
    fst (Symbols.alloc_data syms name)
  ) Symbols.empty input.symbolic in

  (* 2. Encode assembly + allocate code addresses *)
  let syms, encoded_threads = List.fold_left (fun (syms, acc) (thread : Input.thread) ->
    let enc = Assembler.encode ~command thread.code in
    let total_size = List.fold_left (+) 0 enc.widths in
    let syms, code_addr = Symbols.alloc_code syms total_size in
    (syms, (thread, enc, code_addr) :: acc)
  ) (syms, []) input.threads in
  let encoded_threads = List.rev encoded_threads in

  (* 3. Build registers *)
  let registers = List.map (fun (thread, _enc, code_addr) ->
    build_registers syms code_addr thread
  ) encoded_threads in

  (* 4. Build memory *)
  let code_memory = List.map (fun (_thread, enc, code_addr) ->
    build_code_memory code_addr enc
  ) encoded_threads in

  let data_memory = List.map (fun name ->
    let addr = Option.get (Symbols.resolve syms name) in
    let init_value = match List.assoc_opt name input.locations with
      | Some v -> v | None -> "0"
    in
    build_data_memory name addr init_value
  ) input.symbolic in

  (* 5. Build termination conditions *)
  let term_cond = List.map (fun (_thread, (enc : Assembler.encoded), code_addr) ->
    let total_size = List.fold_left (+) 0 enc.widths in
    let end_pc = Z.add code_addr (Z.of_int total_size) in
    [(Reg.pc, RegVal.Number end_pc)]
  ) encoded_threads in

  (* 6. Parse assertions *)
  let finals = Assertion.to_final_conds
    ~expect:input.expect ~syms input.assertion in

  (* 7. Assemble Litmus.Spec.t *)
  { Spec.
    arch = input.arch;
    name = input.name;
    registers;
    memory = code_memory @ data_memory;
    term_cond;
    finals;
  }
