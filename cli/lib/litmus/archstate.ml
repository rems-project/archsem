(** Spec.t to ArchState.t conversion.

    Converts Spec register values (RegVal.gen) to concrete RegVal.t
    via RegVal.of_gen, inserts memory blocks into MemMap, and compiles
    termination conditions into closures. *)

open Archsem

(** {1 Helpers} *)

let of_gen_exn section name reg gen =
  match RegVal.of_gen reg gen with
  | Ok rv -> rv
  | Error msg -> failwith (Printf.sprintf "%s %s: %s" section name msg)

(** Read [step] bytes from [data] at [offset] as a little-endian Z.t. *)
let read_le data offset step =
  let v = ref Z.zero in
  for j = step - 1 downto 0 do
    v := Z.add (Z.shift_left !v 8)
      (Z.of_int (Char.code (Bytes.get data (offset + j))))
  done;
  !v

(** Convert a memory block's data bytes into MemMap entries. *)
let insert_memory_block mm (block : Spec.memory_block) =
  let base = Z.to_int block.base in
  let len = Bytes.length block.data in
  let step = block.step in
  let rec loop addr offset mm =
    if offset >= len then mm
    else
      let v = read_le block.data offset step in
      loop (addr + step) (offset + step) (MemMap.insert addr step v mm)
  in
  loop base 0 mm

(** {1 Conversion} *)

(** Convert Spec.t into ArchState.t, termination conditions, and final conditions. *)
let spec_to_archstate (test : Spec.t) =
  let regs = test.registers |> List.map (fun reg_list ->
    List.fold_left (fun rm (reg, gen) ->
      RegMap.insert (of_gen_exn "[[registers]]" (Reg.to_string reg) reg gen) rm
    ) RegMap.empty reg_list) in
  let mem = test.memory |> List.fold_left insert_memory_block MemMap.empty in
  let init = ArchState.make regs mem in
  let num_threads = List.length regs in
  let term = test.term_cond |> List.map (fun reqs ->
    let parsed = List.map (fun (reg, gen) ->
      (reg, of_gen_exn "[[termCond]]" (Reg.to_string reg) reg gen)
    ) reqs in
    fun rm ->
      List.for_all (fun (reg, exp) ->
        match RegMap.get_opt reg rm with
        | Some actual -> exp = actual
        | None ->
          failwith ("[[termCond]] register not found in thread state: "
            ^ Reg.to_string reg)
      ) parsed) in
  if List.length term <> num_threads then
    failwith (Printf.sprintf
      "[[termCond]] count (%d) must match [[registers]] thread count (%d)"
      (List.length term) num_threads);
  let finals = test.finals in
  (init, term, finals)
