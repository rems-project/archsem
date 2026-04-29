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

(** Assemble code into a [Bytes.t] *)
let assemble (asm : string) : Bytes.t =
  let assemble_cmd = get_assemble_cmd () in
  let extract_cmd = get_extract_cmd () in
  let obj_path = Filename.temp_file "archsem_asm" ".o" in
  let bin_path = Filename.temp_file "archsem_asm" ".bin" in
  Fun.protect
    ~finally:(fun () ->
      (try Sys.remove obj_path with _ -> ());
      try Sys.remove bin_path with _ -> ()
    )
    (fun () ->
       run_cmd "echo %s | %s -o %s" (Filename.quote asm) assemble_cmd
         (Filename.quote obj_path);
       run_cmd "%s %s %s" extract_cmd (Filename.quote obj_path)
         (Filename.quote bin_path);
       read_file_bytes bin_path
     )
