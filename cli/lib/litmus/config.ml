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

(** Run [f], turning TOML errors into fatal config errors *)
let with_config_errors f =
  try f () with
  | Toml.Path_error (path, Toml.FieldMissing field) ->
      Error.fatal "TOML error in config: path %s: Missing field: %s"
        (String.concat "." path) field
  | Toml.Path_error (path, Toml.GenError msg) ->
      Error.fatal "TOML error in config: path %s: %s" (String.concat "." path) msg

(** Builds a generic config getter that memoizes the results without parsing the
    TOML again *)
let make_getter ?default getter path =
  let x = ref None in
  fun () ->
    match !x with
    | Some content -> content
    | None ->
        let content =
          with_config_errors (fun () ->
            match default with
            | None -> Toml.find (get ()) getter path
            | Some default -> Toml.find_or ~default (get ()) getter path
          )
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

(** {1 Profiles}

    A profile [p] is a [profile.p] table that overrides parts of the config.
    Currently only [profile.p.registers.defaults] is supported, which overrides
    [registers.defaults] key by key. The profile is either selected on the CLI
    with [set_profile], or by default with [page_table_setup_default_profile]
    for tests having a [page_table_setup]. *)

(** The profile selected on the CLI if any *)
let cli_profile : string option ref = ref None

let profile_exists name =
  with_config_errors (fun () ->
    Toml.find_opt (get ()) Toml.get_table ["profile"; name] |> Option.is_some
  )

(** Select a profile for all tests, overriding the default selection *)
let set_profile profile =
  Option.iter
    (fun name ->
       if not (profile_exists name) then
         Error.fatal "config: unknown profile %s" name
     )
    profile;
  cli_profile := profile

let get_page_table_setup_default_profile =
  make_getter ~default:None
    (fun toml -> Some (Toml.get_string toml))
    ["page_table_setup_default_profile"]

(** The profile to use for a test, depending on whether it has a
    [page_table_setup]. Memoized for both values of [page_table_setup] *)
let select_profile =
  let memo = Hashtbl.create 2 in
  fun ~page_table_setup ->
    match Hashtbl.find_opt memo page_table_setup with
    | Some profile -> profile
    | None ->
        let profile =
          match !cli_profile with
          | Some _ as profile -> profile
          | None when not page_table_setup -> None
          | None ->
              let profile = get_page_table_setup_default_profile () in
              Option.iter
                (fun name ->
                   if not (profile_exists name) then
                     Error.fatal
                       "config: page_table_setup_default_profile: unknown \
                        profile %s"
                        name
                 )
                profile;
              profile
        in
        Hashtbl.add memo page_table_setup profile;
        profile

(** Builds a config getter that depends on the profile and memoizes the result
    for each profile. [getter] parses the value at [path] and, if the profile
    [p] defines it, the value at [profile.p.path]. Then [merger default override]
    combines them. *)
let make_getter_profile getter merger path =
  let memo = Hashtbl.create 2 in
  fun profile ->
    match Hashtbl.find_opt memo profile with
    | Some content -> content
    | None ->
        let content =
          with_config_errors (fun () ->
            let default = Toml.find (get ()) getter path in
            let in_profile name =
              Toml.find_opt (get ()) getter (["profile"; name] @ path)
            in
            match Option.bind profile in_profile with
            | None -> default
            | Some override -> merger default override
          )
        in
        Hashtbl.add memo profile content;
        content

(** Same as [make_getter_profile], but the getter selects the profile itself
    depending on whether the test has a [page_table_setup] *)
let make_getter_selected_profile getter merger path =
  let get_profile = make_getter_profile getter merger path in
  fun ~page_table_setup -> get_profile (select_profile ~page_table_setup)
