(** Rewrite non-shareable TLBI instructions to inner-shareable (IS) variants.
    The model only supports IS variants, and for single-core semantics they're equivalent. *)
let rewrite_tlbi_to_is asm_str =
  (* TLBI variants with register operand: VAE1, VALE1, VAAE1, VAALE1, ASIDE1, etc. *)
  let with_reg_patterns = [
    (* EL1 variants *)
    "VAE1"; "VALE1"; "VAAE1"; "VAALE1"; "ASIDE1";
    (* EL2 variants *)
    "VAE2"; "VALE2"; "IPAS2E1"; "IPAS2LE1";
    (* EL3 variants *)
    "VAE3"; "VALE3";
  ] in
  (* TLBI variants without register operand *)
  let no_reg_patterns = [
    "VMALLE1"; "VMALLS12E1"; "ALLE1"; "ALLE2"; "ALLE3"; "ALLE1IS"; "ALLE2IS"; "ALLE3IS";
  ] in
  let result = ref asm_str in
  (* Rewrite variants with register: "TLBI VAE1,Xn" -> "TLBI VAE1IS,Xn" *)
  List.iter (fun op ->
    (* Match "TLBI op," but not "TLBI opIS," (case insensitive) *)
    let pattern = Str.regexp_case_fold (Printf.sprintf "\\(TLBI[ \t]+\\)\\(%s\\)\\([ \t]*,\\)" op) in
    result := Str.global_replace pattern (Printf.sprintf "\\1\\2IS\\3") !result
  ) with_reg_patterns;
  (* Rewrite variants without register: "TLBI VMALLE1" -> "TLBI VMALLE1IS" *)
  List.iter (fun op ->
    (* Only rewrite if not already IS variant *)
    if not (Str.string_match (Str.regexp_case_fold ".*IS$") op 0) then begin
      let pattern = Str.regexp_case_fold (Printf.sprintf "\\(TLBI[ \t]+\\)\\(%s\\)\\([ \t]*\\($\\|[\n\r]\\)\\)" op) in
      result := Str.global_replace pattern (Printf.sprintf "\\1\\2IS\\3") !result
    end
  ) no_reg_patterns;
  !result

let encode_assembly ?(arch="aarch64") asm_str =
  (* Rewrite non-shareable TLBI to IS variants *)
  let asm_str = rewrite_tlbi_to_is asm_str in
  (* Create a temporary file for the assembly code *)
  let asm_file = Filename.temp_file "asm_" ".s" in
  (* Create a temporary file for the object code *)
  let obj_file = Filename.temp_file "obj_" ".o" in
  (* Create a temporary file for the binary output *)
  let bin_file = Filename.temp_file "bin_" ".bin" in

  let oc = open_out asm_file in
  Printf.fprintf oc ".text\n.globl _start\n_start:\n%s\n" asm_str;
  close_out oc;

  (* Assemble the code using llvm-mc *)
  (* Using -triple=aarch64-unknown-linux-gnu for generic AArch64 support *)
  let triple = String.lowercase_ascii arch in
  let cmd_assemble = Printf.sprintf "llvm-mc -filetype=obj -triple=%s -mattr=+rcpc,+v8.3a -o %s %s" triple obj_file asm_file in
  if Sys.command cmd_assemble <> 0 then
    failwith ("Failed to assemble code: " ^ asm_str);

  (* Extract larger text section using llvm-objcopy *)
  let cmd_objcopy = Printf.sprintf "llvm-objcopy -O binary %s %s" obj_file bin_file in
  if Sys.command cmd_objcopy <> 0 then
    failwith "Failed to extract binary";

  (* Read the binary file and return as list of integers *)
  let ic = open_in_bin bin_file in
  let len = in_channel_length ic in
  let bytes = Bytes.create len in
  really_input ic bytes 0 len;
  close_in ic;

  (* Clean up temporary files *)
  Sys.remove asm_file;
  Sys.remove obj_file;
  Sys.remove bin_file;

  Printf.eprintf "DEBUG: Input Assembly:\n%s\n" asm_str;

  let rec bytes_to_ints acc i =
    if i >= len then List.rev acc
    else
      let b0 = int_of_char (Bytes.get bytes i) in
      let b1 = int_of_char (Bytes.get bytes (i+1)) in
      let b2 = int_of_char (Bytes.get bytes (i+2)) in
      let b3 = int_of_char (Bytes.get bytes (i+3)) in
      let word = (b3 lsl 24) lor (b2 lsl 16) lor (b1 lsl 8) lor b0 in
      bytes_to_ints (word :: acc) (i + 4)
  in
  let raw_instrs = bytes_to_ints [] 0 in
  Printf.eprintf "DEBUG: Encoded Instructions (Before Rewrite): [%s]\n" (String.concat ", " (List.map (Printf.sprintf "0x%x") raw_instrs));
  raw_instrs
