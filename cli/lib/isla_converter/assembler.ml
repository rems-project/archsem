(** Assembly encoder for isla-to-archsem conversion.

    This module encodes assembly instructions to machine code using llvm-mc.

    Requires: llvm-mc and llvm-objcopy in PATH. *)

(** AArch64 instruction size in bytes (all instructions are 32-bit/4 bytes) *)
let instruction_size = 4

(** Convert raw bytes to a list of 32-bit little-endian integers.
    Each 4 bytes are combined into one instruction word. *)
let bytes_to_instructions bytes len =
  let rec loop acc i =
    if i >= len then List.rev acc
    else
      let b0 = int_of_char (Bytes.get bytes i) in
      let b1 = int_of_char (Bytes.get bytes (i + 1)) in
      let b2 = int_of_char (Bytes.get bytes (i + 2)) in
      let b3 = int_of_char (Bytes.get bytes (i + 3)) in
      let word = (b3 lsl 24) lor (b2 lsl 16) lor (b1 lsl 8) lor b0 in
      loop (word :: acc) (i + instruction_size)
  in
  loop [] 0

(** Clean up temporary files, ignoring errors if files don't exist *)
let cleanup_temp_files files =
  List.iter (fun f -> try Sys.remove f with Sys_error _ -> ()) files

(** [encode_assembly ~arch asm_str] assembles [asm_str] using llvm-mc and returns
    a list of 32-bit instruction words. The [arch] parameter specifies the target
    architecture triple (default: "aarch64"). *)
let encode_assembly ?(arch="aarch64") asm_str =
  (* Create temporary files for the assembly pipeline *)
  let asm_file = Filename.temp_file "asm_" ".s" in
  let obj_file = Filename.temp_file "obj_" ".o" in
  let bin_file = Filename.temp_file "bin_" ".bin" in
  let temp_files = [asm_file; obj_file; bin_file] in

  (* Write assembly source with standard preamble *)
  let oc = open_out asm_file in
  Printf.fprintf oc ".text\n.globl _start\n_start:\n%s\n" asm_str;
  close_out oc;

  (* Assemble using llvm-mc with AArch64 extensions enabled *)
  let triple = String.lowercase_ascii arch in
  let cmd_assemble = Printf.sprintf
    "llvm-mc -filetype=obj -triple=%s -mattr=+rcpc,+v8.3a -o %s %s"
    triple obj_file asm_file in
  if Sys.command cmd_assemble <> 0 then begin
    cleanup_temp_files temp_files;
    failwith ("Failed to assemble code: " ^ asm_str)
  end;

  (* Extract raw binary using llvm-objcopy *)
  let cmd_objcopy = Printf.sprintf "llvm-objcopy -O binary %s %s" obj_file bin_file in
  if Sys.command cmd_objcopy <> 0 then begin
    cleanup_temp_files temp_files;
    failwith "Failed to extract binary"
  end;

  (* Read the binary output *)
  let ic = open_in_bin bin_file in
  let len = in_channel_length ic in
  let bytes = Bytes.create len in
  really_input ic bytes 0 len;
  close_in ic;

  (* Clean up and convert to instruction list *)
  cleanup_temp_files temp_files;
  bytes_to_instructions bytes len
