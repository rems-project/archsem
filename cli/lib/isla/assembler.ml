(** Assembly encoding via external toolchain.

    Uses llvm-mc --show-encoding to get per-instruction byte encodings.
    Works for both fixed-width (AArch64) and variable-width (x86) ISAs. *)

type encoded = {
  bytes : int list;
  widths : int list;
}

(** Run a shell command with [input] on stdin and return stdout. *)
let run_command ~command input =
  let cmd = Printf.sprintf "printf '%%s' %s | %s"
    (Filename.quote input) command in
  let ic = Unix.open_process_in cmd in
  let buf = Buffer.create 256 in
  (try while true do Buffer.add_char buf (input_char ic) done
   with End_of_file -> ());
  let status = Unix.close_process_in ic in
  match status with
  | Unix.WEXITED 0 -> Buffer.contents buf
  | _ -> failwith (Printf.sprintf "assembler failed: %s" cmd)

(** Find substring [needle] in [haystack], returning the index or -1. *)
let find_substring haystack needle =
  let nlen = String.length needle in
  let hlen = String.length haystack in
  let rec go i =
    if i + nlen > hlen then -1
    else if String.sub haystack i nlen = needle then i
    else go (i + 1)
  in
  go 0

(** Parse "encoding: [0x41,0x05,0x80,0xd2]" from a line. *)
let parse_encoding_line line =
  let marker = "encoding: [" in
  let i = find_substring line marker in
  if i < 0 then None
  else
    let start = i + String.length marker in
    match String.index_from_opt line start ']' with
    | None -> None
    | Some j ->
      let hex_part = String.sub line start (j - start) in
      let byte_strs = String.split_on_char ',' hex_part in
      let bytes = List.map (fun s -> int_of_string (String.trim s)) byte_strs in
      Some bytes

(** Convert a list of bytes (little-endian) into a single int word. *)
let le_bytes_to_word bytes =
  List.fold_right (fun b acc -> (acc lsl 8) lor b) bytes 0

(** Parse all encoding lines from llvm-mc --show-encoding output. *)
let parse_encodings output =
  let lines = String.split_on_char '\n' output in
  List.filter_map (fun line ->
    match parse_encoding_line line with
    | None -> None
    | Some bytes ->
      Some (le_bytes_to_word bytes, List.length bytes)
  ) lines

let encode ~command asm =
  let output = run_command ~command asm in
  let pairs = parse_encodings output in
  if pairs = [] then
    failwith "assembler: no instructions encoded";
  let bytes, widths = List.split pairs in
  { bytes; widths }
