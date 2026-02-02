(** Assembly encoder for isla-to-archsem conversion.

    Encodes assembly instructions to machine code using a configurable
    assembler backend (llvm-mc or GNU as). *)

(** AArch64 instruction size in bytes (all instructions are 32-bit/4 bytes) *)
let instruction_size = 4

(** Assembler backend configuration *)
type backend =
  | LLVM of string  (** LLVM toolchain prefix, e.g. "llvm" for llvm-mc/llvm-objcopy *)
  | GNU of string   (** GNU toolchain prefix, e.g. "aarch64-linux-gnu" for aarch64-linux-gnu-as *)

(** Current assembler backend. Defaults to LLVM. *)
let current_backend = ref (LLVM "llvm")

let set_backend b = current_backend := b

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

let cleanup_temp_files files =
  List.iter (fun f -> try Sys.remove f with Sys_error _ -> ()) files

(** Read binary file into instruction list *)
let read_binary bin_file =
  let ic = open_in_bin bin_file in
  let len = in_channel_length ic in
  let bytes = Bytes.create len in
  really_input ic bytes 0 len;
  close_in ic;
  bytes_to_instructions bytes len

(** Assemble using LLVM toolchain (llvm-mc + llvm-objcopy) *)
let encode_llvm prefix ~arch asm_str =
  let asm_file = Filename.temp_file "asm_" ".s" in
  let obj_file = Filename.temp_file "obj_" ".o" in
  let bin_file = Filename.temp_file "bin_" ".bin" in
  let temp_files = [asm_file; obj_file; bin_file] in
  let oc = open_out asm_file in
  Printf.fprintf oc ".text\n.globl _start\n_start:\n%s\n" asm_str;
  close_out oc;
  let mc = prefix ^ "-mc" in
  let objcopy = prefix ^ "-objcopy" in
  let triple = String.lowercase_ascii arch in
  let cmd_asm = Printf.sprintf "%s -filetype=obj -triple=%s -mattr=+rcpc,+v8.3a -o %s %s 2>&1"
    mc triple obj_file asm_file in
  let exit_code = Sys.command cmd_asm in
  if exit_code <> 0 then begin
    cleanup_temp_files temp_files;
    failwith (Printf.sprintf "Failed to assemble with %s (exit %d): %s" mc exit_code asm_str)
  end;
  let cmd_obj = Printf.sprintf "%s -O binary %s %s 2>&1" objcopy obj_file bin_file in
  if Sys.command cmd_obj <> 0 then begin
    cleanup_temp_files temp_files;
    failwith (Printf.sprintf "Failed to extract binary with %s" objcopy)
  end;
  let result = read_binary bin_file in
  cleanup_temp_files temp_files;
  result

(** Assemble using GNU toolchain (prefix-as + prefix-objcopy) *)
let encode_gnu prefix ~arch:_ asm_str =
  let asm_file = Filename.temp_file "asm_" ".s" in
  let obj_file = Filename.temp_file "obj_" ".o" in
  let bin_file = Filename.temp_file "bin_" ".bin" in
  let temp_files = [asm_file; obj_file; bin_file] in
  let oc = open_out asm_file in
  Printf.fprintf oc ".text\n.globl _start\n_start:\n%s\n" asm_str;
  close_out oc;
  let as_cmd = prefix ^ "-as" in
  let objcopy = prefix ^ "-objcopy" in
  let cmd_asm = Printf.sprintf "%s -march=armv8.3-a -o %s %s 2>&1" as_cmd obj_file asm_file in
  let exit_code = Sys.command cmd_asm in
  if exit_code <> 0 then begin
    cleanup_temp_files temp_files;
    failwith (Printf.sprintf "Failed to assemble with %s (exit %d): %s" as_cmd exit_code asm_str)
  end;
  let cmd_obj = Printf.sprintf "%s -O binary %s %s 2>&1" objcopy obj_file bin_file in
  if Sys.command cmd_obj <> 0 then begin
    cleanup_temp_files temp_files;
    failwith (Printf.sprintf "Failed to extract binary with %s" objcopy)
  end;
  let result = read_binary bin_file in
  cleanup_temp_files temp_files;
  result

(** [encode_assembly ~arch asm_str] assembles [asm_str] using the configured
    backend and returns a list of 32-bit instruction words. *)
let encode_assembly ?(arch="aarch64") asm_str =
  match !current_backend with
  | LLVM prefix -> encode_llvm prefix ~arch asm_str
  | GNU prefix -> encode_gnu prefix ~arch asm_str
