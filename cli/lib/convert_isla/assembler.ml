(* --- Assembly Encoding --- *)
let encode_assembly asm_code =
  let temp_asm = Filename.temp_file "asm" ".s" in
  let temp_obj = Filename.temp_file "asm" ".o" in
  let temp_bin = Filename.temp_file "asm" ".bin" in
  let oc = open_out temp_asm in output_string oc asm_code; close_out oc;

  let cmd1 = Printf.sprintf "llvm-mc -triple=aarch64 -filetype=obj -o %s %s"
     (Filename.quote temp_obj) (Filename.quote temp_asm) in
  if Sys.command cmd1 <> 0 then (Printf.eprintf "[Error] Assembler failed\n"; []) else

  let cmd2 = Printf.sprintf "llvm-objcopy -O binary %s %s"
     (Filename.quote temp_obj) (Filename.quote temp_bin) in
  if Sys.command cmd2 <> 0 then (Printf.eprintf "[Error] Objcopy failed\n"; []) else

  let ic = open_in_bin temp_bin in
  let len = in_channel_length ic in
  let buffer = Bytes.create len in
  really_input ic buffer 0 len;
  close_in ic;

  let ints = ref [] in
  for i = 0 to (len / 4) - 1 do
    let offset = i * 4 in
    let b0 = Char.code (Bytes.get buffer offset) in
    let b1 = Char.code (Bytes.get buffer (offset+1)) in
    let b2 = Char.code (Bytes.get buffer (offset+2)) in
    let b3 = Char.code (Bytes.get buffer (offset+3)) in
    let instr = (b3 lsl 24) lor (b2 lsl 16) lor (b1 lsl 8) lor b0 in
    ints := instr :: !ints
  done;
  List.rev !ints
