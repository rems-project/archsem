(** Assemble code via external toolchain. *)

open Litmus

(** Get the assembler command *)
let get_assemble_cmd () =
  Otoml.find (Config.get ()) Otoml.get_string ["assembler"; "assemble"]

(** Get the extracter command e.g. objcopy *)
let get_extract_cmd () =
  Otoml.find (Config.get ()) Otoml.get_string ["assembler"; "extract"]

(** Run a cmd specified by a format string. Raise [Failure] if the command
    fails *)
let run_cmd fmt =
  let run cmd =
    let rc = Sys.command cmd in
    if rc != 0 then
      Printf.ksprintf failwith "assember: %s failed with code %d" cmd rc
  in
  Printf.ksprintf run fmt

(** Read a file into a [Byte.t] *)
let read_file_bytes path : Bytes.t =
  let ic = open_in_bin path in
  let length = in_channel_length ic in
  let buf = Bytes.create length in
  really_input ic buf 0 length;
  close_in ic;
  buf

let parse_nm_output output =
  let lines = String.split_on_char '\n' output in
  List.filter_map (fun line ->
    let line = String.trim line in
    if line = "" then None
    else
      (* llvm-nm format: "000000000000000c t L0" *)
      match String.split_on_char ' ' line with
      | addr_hex :: _typ :: name :: _ ->
        (try Some (name, int_of_string ("0x" ^ addr_hex))
         with Failure _ -> None)
      | _ -> None)
  lines

let read_labels obj_path =
  let buf = Buffer.create 256 in
  let cmd = Printf.sprintf "llvm-nm %s 2>/dev/null" (Filename.quote obj_path) in
  let ic = Unix.open_process_in cmd in
  (try while true do Buffer.add_char buf (input_char ic) done
   with End_of_file -> ());
  let _ = Unix.close_process_in ic in
  parse_nm_output (Buffer.contents buf)

(** Assemble code into a [Bytes.t] and extract labels *)
let assemble (asm : string) : Bytes.t * (string * int) list =
  let assemble_cmd = get_assemble_cmd () in
  let extract_cmd = get_extract_cmd () in
  let obj_path = Filename.temp_file "archsem_asm" ".o" in
  let bin_path = Filename.temp_file "archsem_asm" ".bin" in
  Fun.protect
    ~finally:(fun () ->
      (try Sys.remove obj_path with _ -> ());
      (try Sys.remove bin_path with _ -> ()))
    (fun () ->
       run_cmd "echo %s | %s -o %s"
         (Filename.quote asm)
         assemble_cmd
         (Filename.quote obj_path);
       let labels = read_labels obj_path in
       run_cmd "%s %s %s"
         extract_cmd
         (Filename.quote obj_path)
         (Filename.quote bin_path);
       (read_file_bytes bin_path, labels))
