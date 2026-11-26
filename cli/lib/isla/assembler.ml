(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
(*      Shreeka Lohani, University of Cambridge                               *)
(*      Zongyuan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
(*                                                                            *)
(*  Redistribution and use in source and binary forms, with or without        *)
(*  modification, are permitted provided that the following conditions        *)
(*  are met:                                                                  *)
(*                                                                            *)
(*   1. Redistributions of source code must retain the above copyright        *)
(*      notice, this list of conditions and the following disclaimer.         *)
(*                                                                            *)
(*   2. Redistributions in binary form must reproduce the above copyright     *)
(*      notice, this list of conditions and the following disclaimer in the   *)
(*      documentation and/or other materials provided with the distribution.  *)
(*                                                                            *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS       *)
(*  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT         *)
(*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS         *)
(*  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE            *)
(*  COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,      *)
(*  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,      *)
(*  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS     *)
(*  OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND    *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR     *)
(*  TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE    *)
(*  USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.  *)
(*                                                                            *)
(******************************************************************************)

(** Assembler pipeline: .s generation → clang (assemble+link) → linksem ELF parsing *)

module Linksem_error = Error
open Litmus

(* {1 Types} *)

(** A code section with a preassigned address. *)
type section =
  { name : string;
    code : string;
    addr : int
  }

(** A data symbol with a preassigned address. *)
type data_symbol =
  { name : string;
    addr : int
  }

(** Input to the assembler pipeline *)
type assembly_input =
  { sections : section list;
    symbols : data_symbol list
  }

(** A resolved section with its address and machine code *)
type linked_section =
  { name : string;
    addr : int;
    data : Bytes.t
  }

(** Output of the assembler pipeline *)
type assembly_result =
  { sections : linked_section list;
    symbols : (string * int) list
  }

(* {1 Utilities} *)

exception
  Command_failed of
    { code : int;
      cmd : string;
      stderr : string
    }

(* Run [cmd] in directory [cwd], which receives its stderr. [cmd] is reported
   without [cwd], so with paths relative to [cwd] the failure does not depend on
   where the temporary directory is. *)
let run_cmd ~cwd fmt =
  let run cmd =
    let err_path = Filename.concat cwd "stderr" in
    let full_cmd =
      Printf.sprintf "(cd %s && %s) 2>%s" (Filename.quote cwd) cmd
        (Filename.quote err_path)
    in
    let rc = Sys.command full_cmd in
    if rc <> 0 then
      let err_msg =
        try String.trim (In_channel.with_open_text err_path In_channel.input_all)
        with Sys_error _ -> ""
      in
      raise (Command_failed {code = rc; cmd; stderr = err_msg})
  in
  Printf.ksprintf run fmt

let write_file path content =
  Out_channel.with_open_text path (fun oc -> output_string oc content)

(* Remove [dir] and the files directly inside it. *)
let remove_dir dir =
  Array.iter
    (fun file ->
       try Sys.remove (Filename.concat dir file) with Sys_error _ -> ()
     )
    (try Sys.readdir dir with Sys_error _ -> [||]);
  try Sys.rmdir dir with Sys_error _ -> ()

(* {1 Dump support}

   Optional preservation of assembler intermediate artifacts (.s, .ld,
   .elf) for debugging.  Activated by the [--asm-dump DIR] CLI flag,
   which calls [set_dump_dir].  Artifacts are copied to [DIR] using a
   caller-provided basename. *)

let dump_dir_ref : string option ref = ref None

let set_dump_dir d = dump_dir_ref := d

let dump_dir () = !dump_dir_ref

let copy_file src dst =
  let content = In_channel.with_open_bin src In_channel.input_all in
  Out_channel.with_open_bin dst (fun oc -> output_string oc content)

let dump_artifact dir basename src ~ext =
  copy_file src (Filename.concat dir (basename ^ ext))

(* {1 Stage 1: .s generation} *)

let emit_global buf name = Printf.bprintf buf "\t.global %s\n" name

let emit_label buf name = Printf.bprintf buf "%s:\n" name

(* Section flags for GAS (GNU Assembler) .section directive:
   "a" = allocatable (loaded into memory at runtime)
   "x" = executable (code) *)
let emit_code_section_dir buf name =
  Printf.bprintf buf "\t.section .%s, \"ax\"\n" name

let emit_code_section buf (sec : section) =
  emit_code_section_dir buf sec.name;
  emit_global buf sec.name;
  emit_label buf sec.name;
  Buffer.add_string buf sec.code;
  if sec.code <> "" && sec.code.[String.length sec.code - 1] <> '\n' then
    Buffer.add_char buf '\n'

(* Name of the linker-script symbol that holds the address of data symbol
   [name]. The "." keeps it out of the archsem identifiers read from the ELF. *)
let linker_name name = "__archsem." ^ name

(* [.equiv] aliases the data symbol to its undefined linker symbol, so code
   references stay relocations instead of being folded into constants (as with
   [.set name, addr]), and the assembler rejects any label of the same name. *)
let emit_data_symbol buf (sym : data_symbol) =
  Printf.bprintf buf "\t.equiv %s, %s\n" sym.name (linker_name sym.name)

(** Combine all sections into a single assembly string. Each data symbol is an
    alias of a symbol defined by the linker script. *)
let generate_asm (symbols : data_symbol list) (sections : section list) : string =
  let buf = Buffer.create 256 in
  List.iter (emit_data_symbol buf) symbols;
  List.iter (emit_code_section buf) sections;
  Buffer.contents buf

(* {1 Stage 1b: linker script generation} *)

let emit_ld_symbol buf (sym : data_symbol) =
  Printf.bprintf buf "%s = 0x%x;\n" (linker_name sym.name) sym.addr

let emit_ld_section buf (sec : section) =
  Printf.bprintf buf "  .%s 0x%x : { *(.%s) }\n" sec.name sec.addr sec.name

(** Generate a linker script that defines the linker symbol of each data symbol
    as an absolute symbol and pins each code section [.<name>] to its
    preassigned address. Absolute symbols occupy no section, so distant data
    addresses do not produce large ELF segments. *)
let generate_linker_script (symbols : data_symbol list) (sections : section list)
  : string
  =
  let buf = Buffer.create 256 in
  List.iter (emit_ld_symbol buf) symbols;
  Printf.bprintf buf "SECTIONS {\n";
  List.iter (emit_ld_section buf)
    (List.sort (fun (a : section) b -> compare a.addr b.addr) sections);
  Printf.bprintf buf "}\n";
  Buffer.contents buf

(* {1 Stage 2: clang assemble + link} *)

let get_command = Config.make_getter Toml.get_string ["assembler"; "command"]

(* Name of the artifact [basename ^ ext], relative to the working directory.
   The "./" prefix stops a leading "-" from being read as an option. *)
let artifact_name basename ext =
  let name = basename ^ ext in
  if String.starts_with ~prefix:"-" name then "./" ^ name else name

(** Run clang in [dir] to assemble and link in one step, writing
    [artifact_name basename ".elf"] there. Relative paths keep clang's
    diagnostics independent of [dir]. The caller owns [dir]. *)
let run_pipeline
      ~dir
      ~basename
      (symbols : data_symbol list)
      (sections : section list) : unit
  =
  let command = get_command () in
  let asm_name = artifact_name basename ".s" in
  let ld_name = artifact_name basename ".ld" in
  let elf_name = artifact_name basename ".elf" in
  write_file (Filename.concat dir asm_name) (generate_asm symbols sections);
  write_file
    (Filename.concat dir ld_name)
    (generate_linker_script symbols sections);
  (* -nostdlib: don't link any standard library or startup files.
     -Wl,-e,0: pass -e 0 to the linker — disables the default entry
     symbol by setting the entry address to 0 (we don't have main).
     -Wl,-T,<path>: pass the linker script we generated. *)
  run_cmd ~cwd:dir "%s -nostdlib -Wl,-e,0 -Wl,-T,%s -o %s %s" command
    (Filename.quote ld_name) (Filename.quote elf_name) (Filename.quote asm_name);
  (* Dump intermediate artifacts if configured *)
  match dump_dir () with
  | None -> ()
  | Some dump ->
      List.iter
        (fun (name, ext) ->
           dump_artifact dump basename (Filename.concat dir name) ~ext
         )
        [(asm_name, ".s"); (ld_name, ".ld"); (elf_name, ".elf")]

(* {1 Stage 3: linksem ELF parsing} *)

let find_elf_section elf_sections name =
  match
    List.find_opt
      (fun isec ->
         isec.Elf_interpreted_section.elf64_section_name_as_string = name
       )
      elf_sections
  with
  | Some s -> s
  | None -> Error.fatal "assembler: ELF section %S not found" name

let elf_section_addr isec =
  Nat_big_num.to_int isec.Elf_interpreted_section.elf64_section_addr

let elf_section_bytes isec =
  let chars =
    Byte_sequence.char_list_of_byte_sequence
      isec.Elf_interpreted_section.elf64_section_body
  in
  let len = List.length chars in
  let buf = Bytes.create len in
  List.iteri (Bytes.set buf) chars;
  buf

(** Resolve a section from its own named ELF section. *)
let resolve_section elf_sections (sec : section) : linked_section =
  let isec = find_elf_section elf_sections ("." ^ sec.name) in
  let addr = elf_section_addr isec in
  {name = sec.name; addr; data = elf_section_bytes isec}

let parse_elf (elf_path : string) (input : assembly_input) : assembly_result =
  let info =
    Sail_interface.populate_and_obtain_global_symbol_init_info elf_path
  in
  match info with
  | Linksem_error.Fail msg -> Error.fatal "assembler: ELF parse failed: %s" msg
  | Linksem_error.Success (elf_file, _epi, symbol_map) ->
      let symbols =
        List.filter_map
          (fun (name, (_, _, addr, _, _)) ->
             (* Skip symbols that are not valid archsem identifiers. They are
                most probably auto-generated by the assembler (e.g. $x) *)
             if Lexer.is_ident name then Some (name, Nat_big_num.to_int addr)
             else None
           )
          symbol_map
      in
      let sections =
        match elf_file with
        | Elf_file.ELF_File_64 ef ->
            let elf_sections = ef.elf64_file_interpreted_sections in
            List.map (resolve_section elf_sections) input.sections
        | Elf_file.ELF_File_32 _ -> Error.fatal "assembler: only ELF64 supported"
      in
      {sections; symbols}

(* {1 Public API} *)

(** Assemble, link, and parse ELF. Uses config for toolchain commands. *)
let assemble ~filename (input : assembly_input) : assembly_result =
  let basename = Filename.basename filename in
  let dir = Filename.temp_dir "archsem" ".asm" in
  (* Report a failed command only after [dir] is removed: [Error.fatal] exits. *)
  try
    Fun.protect
      ~finally:(fun () -> remove_dir dir)
      (fun () ->
         run_pipeline ~dir ~basename input.symbols input.sections;
         parse_elf (Filename.concat dir (artifact_name basename ".elf")) input
       )
  with Command_failed {code; cmd; stderr} ->
    Error.fatal "assembler: command failed (code %d): %s\n%s" code cmd stderr
