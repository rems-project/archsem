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

(** Global configuration from CLI flags.

    A thin wrapper around Otoml.t. Each consumer queries the
    section and keys it needs. No per-test config. *)

type t = Toml.t

let empty = Toml.TomlTable []

let rec find_from dir relpath =
  let candidate = Filename.concat dir relpath in
  if Sys.file_exists candidate then Some candidate
  else
    let parent = Filename.dirname dir in
    if parent = dir then None else find_from parent relpath

let first_some = List.find_map Fun.id

let default_path_for_arch arch =
  let file = Arch_id.to_string arch ^ ".toml" in
  let relpath = Filename.concat "config" file in
  let exec_dir = Filename.dirname Sys.argv.(0) in
  first_some [find_from (Sys.getcwd ()) relpath; find_from exec_dir relpath]

let of_arch arch =
  match default_path_for_arch arch with
  | Some path -> Toml.Parser.from_file path
  | None ->
      failwith ("config: no default config for arch " ^ Arch_id.to_string arch)

(** {1 Global config} *)

let global : t option ref = ref None

let is_set () = match !global with None -> false | _ -> true

let set config =
  if is_set () then failwith "Setting config a second time";
  global := Some config

let load file = set (Toml.Parser.from_file file)

let get () =
  match !global with
  | None -> failwith "Getting config before loading it"
  | Some conf -> conf

(** {1 Generic getter} *)

(** Builds a generic config getter that memoizes the results without parsing the
    TOML again *)
let make_getter ?default getter path =
  let x = ref None in
  fun () ->
    match !x with
    | Some content -> content
    | None ->
        let content =
          try
            match default with
            | None -> Toml.find (get ()) getter path
            | Some default -> Toml.find_or ~default (get ()) getter path
          with
          | Toml.Path_error (path, Toml.FieldMissing field) ->
              Error.fatal "TOML error in config: path %s: Missing field: %s"
                (String.concat "." path) field
          | Toml.Path_error (path, Toml.GenError msg) ->
              Error.fatal "TOML error in config: path %s: %s"
                (String.concat "." path) msg
        in
        x := Some content;
        content

(** {1 Common fields} *)
let get_arch = make_getter Arch_id.of_toml ["arch"]

let get_fuel = make_getter ~default:1000 Toml.get_positive ["execution"; "fuel"]

(** Return a hash table for register renames in [registers.renames] *)
let get_reg_renames =
  make_getter ~default:(Hashtbl.create 0)
    (fun toml ->
       let list = Toml.get_table_values Toml.get_string toml in
       let tbl = Hashtbl.create (List.length list) in
       List.iter
         (fun (old_name, new_name) -> Hashtbl.add tbl old_name new_name)
         list;
       tbl
     )
    ["registers"; "renames"]

(** Return the renamed version of a register according to [register.renames] *)
let get_reg_rename reg = Hashtbl.find_opt (get_reg_renames ()) reg

(** Return the renamed version of a register according to [register.renames] or
    the orignal if there is no rename *)
let get_reg_rename_or reg = get_reg_rename reg |> Option.value ~default:reg
