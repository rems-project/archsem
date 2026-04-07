(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
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
    data : data_symbol list;
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
          (fun () ->
             let ic = open_in err_path in
             Fun.protect
               ~finally:(fun () -> close_in ic)
               (fun () -> In_channel.input_all ic)
           )
      in
      Printf.ksprintf failwith "assembler: command failed (code %d): %s\n%s" rc
        cmd err_msg
    end;
    try Sys.remove err_path with _ -> ()
  in
  Printf.ksprintf run fmt

let write_file path content =
  let oc = open_out path in
  Fun.protect
    ~finally:(fun () -> close_out oc)
    (fun () -> output_string oc content)

(* {1 Stage 1: .s generation} *)

(** Assembly directive emitters *)
let emit_directive buf name = Printf.bprintf buf "\t.%s\n" name

let emit_global buf name = Printf.bprintf buf "\t.global %s\n" name

let emit_label buf name = Printf.bprintf buf "%s:\n" name

let emit_balign buf n = Printf.bprintf buf "\t.balign %d\n" n

let emit_byte buf b = Printf.bprintf buf "\t.byte 0x%02x\n" (Char.code b)

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

let fixed_and_relocatable (input : assembly_input) =
  List.partition (fun (s : section) -> s.fixed_addr <> None) input.sections

(** Combine all sections into a single assembly string *)
let generate_asm (input : assembly_input) : string =
  let (fixed, relocatable) = fixed_and_relocatable input in
  let buf = Buffer.create 256 in
  (* Data: each symbol in its own section for per-page isolation *)
  List.iter
    (fun (sym : data_symbol) ->
       emit_data_section_dir buf sym.name;
       emit_data_symbol buf sym
     )
    input.symbols;
  (* Fixed-addr sections: each in its own named section *)
  List.iter
    (fun (sec : section) ->
       emit_section_dir buf sec.name;
       emit_code_section buf sec
     )
    fixed;
  (* Relocatable sections: all under shared .text *)
  if relocatable <> [] then begin
    emit_directive buf "text";
    List.iter (emit_code_section buf) relocatable
  end;
  Buffer.contents buf

(* {1 Stage 1b: linker script generation} *)

let base_addr () =
  Otoml.find (Config.get ()) Otoml.get_integer ["isla"; "symbols"; "base_address"]

let page_bits () =
  Otoml.find (Config.get ()) Otoml.get_integer ["isla"; "page_bits"]

(** Compute (section_name, address) pairs for all sections. *)
let compute_section_layout (input : assembly_input) : (string * int) list =
  let base = base_addr () in
  let page_size = 1 lsl page_bits () in
  (* One page per symbol so each lands on a separate page, allowing
     independent page-table attributes (e.g. permissions) per symbol. *)
  let n_data_pages = List.length input.symbols in
  let text_base = base + (n_data_pages * page_size) in
  let (fixed, has_text) =
    let (f, r) = fixed_and_relocatable input in
    (f, r <> [])
  in
  let fixed_sections =
    List.map
      (fun (sec : section) -> ("." ^ sec.name, Option.get sec.fixed_addr))
      fixed
  in
  let data_sections =
    List.mapi
      (fun i (sym : data_symbol) -> (".data." ^ sym.name, base + (i * page_size)))
      input.symbols
  in
  let text_section = if has_text then [(".text", text_base)] else [] in
  data_sections @ text_section @ fixed_sections

let ld_section buf name addr =
  Printf.bprintf buf "  %s 0x%x : { *(%s) }\n" name addr name

(** Generate a linker script from a section layout. *)
let generate_linker_script (input : assembly_input) : string =
  let layout =
    compute_section_layout input |> List.sort (fun a b -> compare (snd a) (snd b))
  in
  let buf = Buffer.create 256 in
  Printf.bprintf buf "SECTIONS {\n";
  List.iter (fun (name, addr) -> ld_section buf name addr) layout;
  Printf.bprintf buf "}\n";
  Buffer.contents buf

(* {1 Stage 2: clang assemble + link} *)

(** Run clang to assemble and link in one step, producing an ELF file.
    Returns the path to the ELF file; caller is responsible for cleanup. *)
let run_pipeline (input : assembly_input) : string =
  let command =
    Otoml.find (Config.get ()) Otoml.get_string ["assembler"; "command"]
  in
  let asm_path = Filename.temp_file "archsem" ".s" in
  let ld_path = Filename.temp_file "archsem" ".ld" in
  let elf_path = Filename.temp_file "archsem" ".elf" in
  Fun.protect
    ~finally:(fun () ->
      List.iter (fun p -> try Sys.remove p with _ -> ()) [asm_path; ld_path]
    )
    (fun () ->
       write_file asm_path (generate_asm input);
       write_file ld_path (generate_linker_script input);
       run_cmd "%s -nostdlib -Wl,-e,0 -Wl,-T,%s -o %s %s" command
         (Filename.quote ld_path) (Filename.quote elf_path)
         (Filename.quote asm_path);
       elf_path
     )

(* {1 Stage 3: linksem ELF parsing} *)

let lookup_symbol_addr symbol_map name =
  match List.assoc_opt name symbol_map with
  | Some (_, _, addr, _, _) -> Nat_big_num.to_int addr
  | None -> Printf.ksprintf failwith "assembler: symbol %S not found in ELF" name

let find_elf_section elf_sections name =
  match
    List.find_opt
      (fun isec ->
         isec.Elf_interpreted_section.elf64_section_name_as_string = name
       )
      elf_sections
  with
  | Some s -> s
  | None -> Printf.ksprintf failwith "assembler: ELF section %S not found" name

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

(** Resolve relocatable sections that share .text, splitting by symbol addresses.
    "Relocatable" follows linker terminology: these sections have no fixed address,
    so the linker assigns their placement.
    Processes all sections together because they share one .text ELF section -
    the .text body and symbol addresses are resolved once, then each section's
    byte range is sliced out by adjacent symbol boundaries. *)
let resolve_relocatable_sections elf_sections symbol_map (secs : section list) :
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

let parse_elf (elf_path : string) (input : assembly_input) : assembly_result =
  let info =
    Sail_interface.populate_and_obtain_global_symbol_init_info elf_path
  in
  match info with
  | Error.Fail msg ->
      Printf.ksprintf failwith "assembler: ELF parse failed: %s" msg
  | Error.Success (elf_file, _epi, symbol_map) ->
      let symbols =
        List.map
          (fun (name, (_, _, addr, _, _)) -> (name, Nat_big_num.to_int addr))
          symbol_map
      in
      let sections =
        match elf_file with
        | Elf_file.ELF_File_64 ef ->
            let elf_sections = ef.elf64_file_interpreted_sections in
            let (fixed, relocatable) = fixed_and_relocatable input in
            List.map (resolve_fixed_section elf_sections) fixed
            @ resolve_relocatable_sections elf_sections symbol_map relocatable
        | Elf_file.ELF_File_32 _ -> failwith "assembler: only ELF64 supported"
      in
      {sections; data = input.symbols; symbols}

(* {1 Public API} *)

(** Assemble, link, and parse ELF. Uses config for toolchain commands. *)
let assemble (input : assembly_input) : assembly_result =
  let elf_path = run_pipeline input in
  Fun.protect
    ~finally:(fun () -> try Sys.remove elf_path with _ -> ())
    (fun () -> parse_elf elf_path input)

(** Look up a symbol address by name. *)
let resolve_symbol (result : assembly_result) (name : string) : int =
  match List.assoc_opt name result.symbols with
  | Some addr -> addr
  | None -> Printf.ksprintf failwith "assembler: symbol %S not found" name
