(** Convert a Testrepr.t into the Rocq types (ArchState.t, MemMap.t, etc.).

    Parameterized by architecture via the Make functor. *)

module Make (Arch : Archsem.Arch) = struct
  open Arch

  let insert_memory_block mm (block : Testrepr.memory_block) =
    MemMap.insertb block.addr block.data mm

  let regmap_of_gen_list reg_list =
    List.fold_left
      (fun rm (name, gen) ->
        RegMap.insert (RegVal.of_string_gen name gen) rm)
      RegMap.empty reg_list

  let regmaps_of_testrepr registers =
    List.map regmap_of_gen_list registers

  let memory_of_testrepr memory =
    List.fold_left insert_memory_block MemMap.empty memory

  let term_cond_of_gen_list reqs =
    let parsed = List.map (fun (name, gen) -> RegVal.of_string_gen name gen) reqs in
    fun rm ->
      List.for_all
        (fun rv ->
          let reg = RegVal.reg rv in
          match RegMap.get_opt reg rm with
          | Some actual -> rv = actual
          | None ->
            failwith
              ("[[termCond]] register not found in thread state: "
             ^ Reg.to_string reg))
        parsed

  let term_conds_of_testrepr term_cond =
    List.map term_cond_of_gen_list term_cond

  let validate_thread_count regs term =
    let num_threads = List.length regs in
    if List.length term <> num_threads then
      failwith
        (Printf.sprintf
           "[[termCond]] count (%d) must match [[registers]] thread count (%d)"
           (List.length term) num_threads)

  (** Convert Testrepr.t into ArchState.t and termination conditions. *)
  let testrepr_to_archstate (test : Testrepr.t) =
    let regs = regmaps_of_testrepr test.registers in
    let mem = memory_of_testrepr test.memory in
    let init = ArchState.make regs mem in
    let term = term_conds_of_testrepr test.term_cond in
    validate_thread_count regs term;
    (init, term)
end
