(** Assembly encoding via external toolchain. *)

open Litmus

let get_assemble_cmd () =
  Otoml.find (Config.get ()) Otoml.get_string ["assembler"; "assemble"]

let get_extract_cmd () =
  Otoml.find (Config.get ()) Otoml.get_string ["assembler"; "extract"]

let run_to_file ~command input out_path =
  let cmd =
    Printf.sprintf "printf '%%s' %s | %s -o %s 2>/dev/null"
      (Filename.quote input)
      command
      (Filename.quote out_path)
  in
  Sys.command cmd

let read_file_bytes path =
  let ic = open_in_bin path in
  let length = in_channel_length ic in
  let buf = Bytes.create length in
  really_input ic buf 0 length;
  close_in ic;
  buf

let assemble asm =
  let assemble_cmd = get_assemble_cmd () in
  let extract_cmd = get_extract_cmd () in
  let obj_path = Filename.temp_file "archsem_asm" ".o" in
  let bin_path = Filename.temp_file "archsem_asm" ".bin" in
  Fun.protect
    ~finally:(fun () ->
      (try Sys.remove obj_path with _ -> ());
      (try Sys.remove bin_path with _ -> ()))
    (fun () ->
      let rc = run_to_file ~command:assemble_cmd asm obj_path in
      if rc <> 0 then
        failwith
          (Printf.sprintf "assembler: assemble command failed (exit %d)" rc);
      let rc =
        Sys.command
          (Printf.sprintf "%s %s %s 2>/dev/null"
             extract_cmd
             (Filename.quote obj_path)
             (Filename.quote bin_path))
      in
      if rc <> 0 then
        failwith
          (Printf.sprintf "assembler: extract command failed (exit %d)" rc);
      read_file_bytes bin_path)
