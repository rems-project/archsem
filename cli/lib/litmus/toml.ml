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

module Numbers = struct
  include Otoml.Base.OCamlNumber

  type int = Z.t

  let int_of_string = Z.of_string

  (* Heuristic: between 0 and 15, we prefer decimal, otherwise hexadecimal *)
  let int_to_string z =
    if Z.numbits z <= 4 then Z.to_string z else Z.format "%#x" z

  let int_of_boolean b = if b then Z.one else Z.zero

  let int_to_boolean n = n != Z.zero

  let float_of_int = Z.to_float

  let int_of_float = Z.of_float
end

include Otoml.Base.Make (Numbers) (Otoml.Base.StringDate)

let toml_type_name : t -> string = function
  | TomlInteger _ -> "integer"
  | TomlFloat _ -> "float"
  | TomlString _ -> "string"
  | TomlBoolean _ -> "boolean"
  | TomlArray _ -> "array"
  | TomlTable _ -> "table"
  | TomlInlineTable _ -> "table"
  | TomlTableArray _ -> "array"
  | _ -> "datetime"

(** {1 Path exception types}
    Change OToml exception to have a path of where the error is coming from
    The path contains ["[n]"] when looking up in an array
*)

type toml_error =
  | GenError of string
  | FieldMissing of string

exception Path_error of string list * toml_error

let error ?(path = []) fmt =
  Printf.ksprintf (fun s -> raise (Path_error (path, GenError s))) fmt

let field_error field = raise (Path_error ([], FieldMissing field))

let _ =
  Printexc.register_printer (function
    | Parse_error (None, msg) -> Some (Printf.sprintf "TOML parse error: %s" msg)
    | Parse_error (Some (line, col), msg) ->
        Some
          (Printf.sprintf "TOML parse error at line %d, character %d: %s" line col
             msg
          )
    | Path_error (path, FieldMissing field) ->
        if path == [] then
          Some (Printf.sprintf "TOML field \"%s\" is missing" field)
        else
          Some
            (Printf.sprintf "TOML field \"%s\" is missing at %s" field
               (String.concat "." path)
            )
    | Path_error (path, GenError msg) ->
        Some
          (Printf.sprintf "TOML error at \"%s\": %s" (String.concat "." path) msg)
    | _ -> None
    )

let get_table toml =
  match toml with
  | TomlTable tbl -> tbl
  | TomlInlineTable tbl -> tbl
  | _ -> error "Expected table, found %s" (toml_type_name toml)

let get_field toml field =
  let tbl = get_table toml in
  try List.assoc field tbl with Not_found -> field_error field

let get_string toml =
  match toml with
  | TomlString s -> s
  | _ -> error "Expected string, found %s" (toml_type_name toml)

let get_array ?(strict = true) accessor toml =
  match toml with
  | TomlArray a | TomlTableArray a ->
      List.mapi
        (fun i v ->
           try accessor v
           with Path_error (path, msg) ->
             raise (Path_error (Printf.sprintf "[%i]" i :: path, msg))
         )
        a
  | _ ->
      if strict then error "Expected array, found %s" (toml_type_name toml)
      else List.map accessor [toml]

let get_table_values accessor toml =
  let tbl = get_table toml in
  List.map
    (fun (k, v) ->
       try (k, accessor v)
       with Path_error (path, msg) -> raise (Path_error (k :: path, msg))
     )
    tbl

let get_table_key_values accessor toml =
  let tbl = get_table toml in
  List.map
    (fun (k, v) ->
       try accessor k v
       with Path_error (path, msg) -> raise (Path_error (k :: path, msg))
     )
    tbl

(** Get singleton table (single entry) *)
let get_singleton accessor toml =
  let tbl = get_table toml in
  match tbl with
  | [(k, v)] -> (
    try accessor k v
    with Path_error (path, msg) -> raise (Path_error (k :: path, msg))
  )
  | _ -> error "Expected singleton table, but got %d entries" (List.length tbl)

let get_Z ?(strict = true) toml =
  match toml with
  | TomlInteger i -> i
  | TomlString s when strict == false -> (
    try Z.of_string s
    with Invalid_argument msg -> error "Expected integer, parsing error %s" msg
  )
  | _ -> error "Expected integer, found %s" (toml_type_name toml)

let get_integer ?(strict = true) toml =
  let z = get_Z ~strict toml in
  try Z.to_int z
  with Z.Overflow -> error "Integer out of bounds (-2^62 to 2^62-1)"

let get_positive ?(strict = true) toml =
  let v = get_integer ~strict toml in
  if v <= 0 then error "Expected positive integer, got %i" v;
  v

let rec find toml accessor path =
  match path with
  | [] -> accessor toml
  | field :: tl -> (
      let next = get_field toml field in
      try find next accessor tl
      with Path_error (path, msg) -> raise (Path_error (field :: path, msg))
    )

let find_opt toml accessor path =
  try Some (find toml accessor path) with Path_error (_, FieldMissing _) -> None

let find_or ~default toml accessor path =
  find_opt toml accessor path |> Option.value ~default
