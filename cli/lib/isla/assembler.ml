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

let run_cmd fmt =
  let run cmd =
    let err_path = Filename.temp_file "archsem" ".err" in
    let full_cmd = Printf.sprintf "%s 2>%s" cmd (Filename.quote err_path) in
    let rc = Sys.command full_cmd in
    if rc <> 0 then begin
      let err_msg =
        Fun.protect
          ~finally:(fun () -> try Sys.remove err_path with _ -> ())
          (fun () -> In_channel.with_open_text err_path In_channel.input_all)
      in
      Error.fatal "assembler: command failed (code %d): %s\n%s" rc cmd err_msg
    end;
    try Sys.remove err_path with _ -> ()
  in
  Printf.ksprintf run fmt

let write_file path content =
  Out_channel.with_open_text path (fun oc -> output_string oc content)

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

(** Combine all sections into a single assembly string. Data symbols are only
    declared global here; the linker script defines them. *)
let generate_asm (symbols : data_symbol list) (sections : section list) : string =
  let buf = Buffer.create 256 in
  List.iter (fun (sym : data_symbol) -> emit_global buf sym.name) symbols;
  List.iter (emit_code_section buf) sections;
  Buffer.contents buf

(* {1 Stage 1b: linker script generation} *)

(* PROVIDE leaves a label of the same name in the code in place, so the caller
   can report the conflict. *)
let emit_ld_symbol buf (sym : data_symbol) =
  Printf.bprintf buf "PROVIDE(%s = 0x%x);\n" sym.name sym.addr

let emit_ld_section buf (sec : section) =
  Printf.bprintf buf "  .%s 0x%x : { *(.%s) }\n" sec.name sec.addr sec.name

(** Generate a linker script that defines each data symbol as an absolute
    symbol and pins each code section [.<name>] to its preassigned address.
    Absolute symbols occupy no section, so distant data addresses do not
    produce large ELF segments. *)
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

(** Run clang to assemble and link in one step, writing an ELF file at
    [elf_path].  The caller owns [elf_path] (creates and cleans it up). *)
let run_pipeline
      ~basename
      ~(elf_path : string)
      (symbols : data_symbol list)
      (sections : section list) : unit
  =
  let command = get_command () in
  let asm_path = Filename.temp_file basename ".s" in
  let ld_path = Filename.temp_file basename ".ld" in
  Fun.protect
    ~finally:(fun () ->
      List.iter (fun p -> try Sys.remove p with _ -> ()) [asm_path; ld_path]
    )
    (fun () ->
       write_file asm_path (generate_asm symbols sections);
       write_file ld_path (generate_linker_script symbols sections);
       (* -nostdlib: don't link any standard library or startup files.
          -Wl,-e,0: pass -e 0 to the linker — disables the default entry
          symbol by setting the entry address to 0 (we don't have main).
          -Wl,-T,<path>: pass the linker script we generated. *)
       run_cmd "%s -nostdlib -Wl,-e,0 -Wl,-T,%s -o %s %s" command
         (Filename.quote ld_path) (Filename.quote elf_path)
         (Filename.quote asm_path);
       (* Dump intermediate artifacts if configured *)
       match dump_dir () with
       | None -> ()
       | Some dir ->
           dump_artifact dir basename asm_path ~ext:".s";
           dump_artifact dir basename ld_path ~ext:".ld";
           dump_artifact dir basename elf_path ~ext:".elf"
     )

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
  let elf_path = Filename.temp_file basename ".elf" in
  Fun.protect
    ~finally:(fun () -> try Sys.remove elf_path with _ -> ())
    (fun () ->
       run_pipeline ~basename ~elf_path input.symbols input.sections;
       parse_elf elf_path input
     )
