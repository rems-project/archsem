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

(** A code section to assemble *)
type section =
  { name : string;
    code : string;
    fixed_addr : int option
  }

(** Data symbol to allocate in .data *)
type data_symbol =
  { name : string;
    init_bytes : Bytes.t
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
   which calls [set_dump_dir].  Artifacts are copied to [DIR] using
   the first section's name as basename. *)

let dump_dir_ref : string option ref = ref None

let set_dump_dir d = dump_dir_ref := d

let dump_dir () = !dump_dir_ref

let copy_file src dst =
  let content = In_channel.with_open_bin src In_channel.input_all in
  Out_channel.with_open_bin dst (fun oc -> output_string oc content)

let dump_basename (fixed : section list) (linker_placed : section list) =
  match (fixed, linker_placed) with
  | (s :: _, _) | (_, s :: _) -> s.name
  | ([], []) -> "empty"

let dump_artifact dir basename src ~ext =
  copy_file src (Filename.concat dir (basename ^ ext))

(* {1 Stage 1: .s generation} *)

(** Assembly directive emitters *)
let emit_directive buf name = Printf.bprintf buf "\t.%s\n" name

let emit_global buf name = Printf.bprintf buf "\t.global %s\n" name

let emit_label buf name = Printf.bprintf buf "%s:\n" name

let emit_balign buf n = Printf.bprintf buf "\t.balign %d\n" n

let emit_byte buf b = Printf.bprintf buf "\t.byte 0x%02x\n" (Char.code b)

(* Section flags for GAS (GNU Assembler) .section directive:
   "a" = allocatable (loaded into memory at runtime)
   "x" = executable (code)
   "w" = writable (data) *)
let emit_section_dir buf name = Printf.bprintf buf "\t.section .%s, \"ax\"\n" name

let emit_data_section_dir buf name =
  Printf.bprintf buf "\t.section .data.%s, \"aw\"\n" name

let emit_data_symbol buf (sym : data_symbol) =
  let size = Bytes.length sym.init_bytes in
  let align = if size >= 8 then 8 else if size >= 4 then 4 else 2 in
  emit_balign buf align;
  emit_global buf sym.name;
  emit_label buf sym.name;
  Bytes.iter (emit_byte buf) sym.init_bytes

let emit_code_section buf (sec : section) =
  emit_global buf sec.name;
  emit_label buf sec.name;
  Buffer.add_string buf sec.code;
  if sec.code <> "" && sec.code.[String.length sec.code - 1] <> '\n' then
    Buffer.add_char buf '\n'

let split_fixed_sections (input : assembly_input) =
  List.partition (fun (s : section) -> s.fixed_addr <> None) input.sections

(** Combine all sections into a single assembly string *)
let generate_asm
      (symbols : data_symbol list)
      (fixed : section list)
      (linker_placed : section list) : string
  =
  let buf = Buffer.create 256 in
  List.iter
    (fun (sym : data_symbol) ->
       emit_data_section_dir buf sym.name;
       emit_data_symbol buf sym
     )
    symbols;
  (* Fixed-addr sections: each in its own named section *)
  List.iter
    (fun (sec : section) ->
       emit_section_dir buf sec.name;
       emit_code_section buf sec
     )
    fixed;
  (* Linker-placed code sections: all under shared .text *)
  if linker_placed <> [] then begin
    emit_directive buf "text";
    List.iter (emit_code_section buf) linker_placed
  end;
  Buffer.contents buf

(* {1 Stage 1b: linker script generation} *)

let page_bits () = Toml.find (Config.get ()) Toml.get_integer ["isla"; "page_bits"]

(** Round [addr] up to the next multiple of [page_size]. *)
let next_page page_size addr = ((addr / page_size) + 1) * page_size

(** Compute (section_name, address) pairs for all sections.

    Layout: fixed-address sections take their requested addresses first.
    Non-fixed sections (data symbols then code) are then placed
    incrementally starting at the page boundary right after the
    highest fixed address; if there are no fixed sections, they start
    at the first non-zero page. *)
let compute_section_layout
      (symbols : data_symbol list)
      (fixed : section list)
      (linker_placed : section list) : (string * int) list
  =
  let page_size = 1 lsl page_bits () in
  let fixed_sorted =
    List.sort
      (fun (a : section) (b : section) ->
         compare (Option.get a.fixed_addr) (Option.get b.fixed_addr)
       )
      fixed
  in
  let fixed_layout =
    List.map
      (fun (sec : section) -> ("." ^ sec.name, Option.get sec.fixed_addr))
      fixed_sorted
  in
  let next_base =
    match List.rev fixed_sorted with
    | [] -> page_size
    | last :: _ -> next_page page_size (Option.get last.fixed_addr)
  in
  let data_layout =
    List.mapi
      (fun i (sym : data_symbol) ->
         (".data." ^ sym.name, next_base + (i * page_size))
       )
      symbols
  in
  let text_addr = next_base + (List.length symbols * page_size) in
  let text_layout = if linker_placed <> [] then [(".text", text_addr)] else [] in
  fixed_layout @ data_layout @ text_layout

let ld_section buf name addr =
  Printf.bprintf buf "  %s 0x%x : { *(%s) }\n" name addr name

(** Generate a linker script from a section layout. *)
let generate_linker_script
      (symbols : data_symbol list)
      (fixed : section list)
      (linker_placed : section list) : string
  =
  let layout =
    compute_section_layout symbols fixed linker_placed
    |> List.sort (fun a b -> compare (snd a) (snd b))
  in
  let buf = Buffer.create 256 in
  Printf.bprintf buf "SECTIONS {\n";
  List.iter (fun (name, addr) -> ld_section buf name addr) layout;
  Printf.bprintf buf "}\n";
  Buffer.contents buf

(* {1 Stage 2: clang assemble + link} *)

(** Run clang to assemble and link in one step, writing an ELF file at
    [elf_path].  The caller owns [elf_path] (creates and cleans it up). *)
let run_pipeline
      ~(elf_path : string)
      (symbols : data_symbol list)
      (fixed : section list)
      (linker_placed : section list) : unit
  =
  let command =
    Toml.find (Config.get ()) Toml.get_string ["assembler"; "command"]
  in
  let asm_path = Filename.temp_file "archsem" ".s" in
  let ld_path = Filename.temp_file "archsem" ".ld" in
  Fun.protect
    ~finally:(fun () ->
      List.iter (fun p -> try Sys.remove p with _ -> ()) [asm_path; ld_path]
    )
    (fun () ->
       write_file asm_path (generate_asm symbols fixed linker_placed);
       write_file ld_path (generate_linker_script symbols fixed linker_placed);
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
           let base = dump_basename fixed linker_placed in
           dump_artifact dir base asm_path ~ext:".s";
           dump_artifact dir base ld_path ~ext:".ld";
           dump_artifact dir base elf_path ~ext:".elf"
     )

(* {1 Stage 3: linksem ELF parsing} *)

let lookup_symbol_addr symbol_map name =
  match List.assoc_opt name symbol_map with
  | Some (_, _, addr, _, _) -> Nat_big_num.to_int addr
  | None -> Error.fatal "assembler: symbol %S not found in ELF" name

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

let elf_section_size isec =
  Nat_big_num.to_int isec.Elf_interpreted_section.elf64_section_size

let elf_section_bytes isec =
  let chars =
    Byte_sequence.char_list_of_byte_sequence
      isec.Elf_interpreted_section.elf64_section_body
  in
  let len = List.length chars in
  let buf = Bytes.create len in
  List.iteri (Bytes.set buf) chars;
  buf

(** Resolve a fixed-addr section from its own named ELF section *)
let resolve_fixed_section elf_sections (sec : section) : linked_section =
  let isec = find_elf_section elf_sections ("." ^ sec.name) in
  let addr = elf_section_addr isec in
  {name = sec.name; addr; data = elf_section_bytes isec}

(* Find the first address after [addr] in a sorted list, or [limit] if last. *)
let next_boundary addr sorted_addrs limit =
  match List.find_opt (fun a -> a > addr) sorted_addrs with
  | Some a -> a
  | None -> limit

(** Resolve linker-placed sections that share .text, splitting by symbol addresses.
    These are the code sections without a fixed address; the linker assigns
    their placement.
    Processes all sections together because they share one .text ELF section -
    the .text body and symbol addresses are resolved once, then each section's
    byte range is sliced out by adjacent symbol boundaries. *)
let resolve_linker_placed_sections elf_sections symbol_map (secs : section list) :
  linked_section list
  =
  match secs with
  | [] -> []
  | _ ->
      let text_sec = find_elf_section elf_sections ".text" in
      let text_base = elf_section_addr text_sec in
      let text_end = text_base + elf_section_size text_sec in
      let text_bytes = elf_section_bytes text_sec in
      let sec_addrs =
        List.map
          (fun (s : section) -> (s, lookup_symbol_addr symbol_map s.name))
          secs
      in
      let all_addrs = List.map snd sec_addrs |> List.sort_uniq compare in
      List.map
        (fun ((sec : section), addr) ->
           let len = next_boundary addr all_addrs text_end - addr in
           { name = sec.name;
             addr;
             data = Bytes.sub text_bytes (addr - text_base) len
           }
         )
        sec_addrs

let parse_elf
      (elf_path : string)
      (fixed : section list)
      (linker_placed : section list) : assembly_result
  =
  let info =
    Sail_interface.populate_and_obtain_global_symbol_init_info elf_path
  in
  match info with
  | Linksem_error.Fail msg -> Error.fatal "assembler: ELF parse failed: %s" msg
  | Linksem_error.Success (elf_file, _epi, symbol_map) ->
      let symbols =
        List.map
          (fun (name, (_, _, addr, _, _)) -> (name, Nat_big_num.to_int addr))
          symbol_map
      in
      let sections =
        match elf_file with
        | Elf_file.ELF_File_64 ef ->
            let elf_sections = ef.elf64_file_interpreted_sections in
            List.map (resolve_fixed_section elf_sections) fixed
            @ resolve_linker_placed_sections elf_sections symbol_map linker_placed
        | Elf_file.ELF_File_32 _ -> Error.fatal "assembler: only ELF64 supported"
      in
      {sections; symbols}

(* {1 Public API} *)

(** Assemble, link, and parse ELF. Uses config for toolchain commands. *)
let assemble (input : assembly_input) : assembly_result =
  let (fixed, linker_placed) = split_fixed_sections input in
  let elf_path = Filename.temp_file "archsem" ".elf" in
  Fun.protect
    ~finally:(fun () -> try Sys.remove elf_path with _ -> ())
    (fun () ->
       run_pipeline ~elf_path input.symbols fixed linker_placed;
       parse_elf elf_path fixed linker_placed
     )

(** Look up a symbol address by name. *)
let resolve_symbol (result : assembly_result) (name : string) : int =
  match List.assoc_opt name result.symbols with
  | Some addr -> addr
  | None -> Printf.ksprintf failwith "assembler: symbol %S not found" name
