(** Isla TOML input parser for isla-to-archsem conversion.

    This module parses isla litmus test TOML files:
    - Page table setup DSL
    - Thread definitions (code, registers)
    - Section definitions (exception handlers)

    Only parses - does not encode assembly or allocate addresses. *)

(** Thread definition from TOML (raw, before encoding) *)
type thread_def = {
  tid: string;
  code: string;  (* Assembly code string *)
  reset_regs: (string * Otoml.t) list;
}

(** Section definition from TOML (raw, before encoding) *)
type section_def = {
  sec_name: string;
  sec_addr: Z.t;
  sec_code: string;  (* Assembly code string *)
}

(** Helper to get optional TOML string *)
let get_string_opt toml keys =
  match Otoml.find_opt toml (fun x -> x) keys with
  | Some (Otoml.TomlString s) -> Some s
  | _ -> None

(** Helper to get optional TOML table *)
let get_table_opt toml keys =
  match Otoml.find_opt toml (fun x -> x) keys with
  | Some (Otoml.TomlTable t) -> Some t
  | _ -> None

(** Parse page_table_setup DSL from TOML *)
let parse_pt_setup toml =
  match get_string_opt toml ["page_table_setup"] with
  | Some s ->
      let lexbuf = Lexing.from_string s in
      (try Parser.main_dsl Lexer.read lexbuf
       with Parser.Error ->
         let pos = Lexing.lexeme_start_p lexbuf in
         failwith (Printf.sprintf "Syntax error at line %d, char %d"
           pos.pos_lnum (pos.pos_cnum - pos.pos_bol)))
  | None -> []

(** Extract register configuration from thread table.
    Supports both 'reset' (pgtable tests) and 'init' (usermode tests) keys. *)
let extract_reset_regs thread_table =
  let try_key key =
    match List.assoc_opt key thread_table with
    | Some (Otoml.TomlTable regs) -> Some regs
    | Some (Otoml.TomlInlineTable regs) -> Some regs
    | _ -> None
  in
  match try_key "reset" with
  | Some regs -> regs
  | None -> (match try_key "init" with Some regs -> regs | None -> [])

(** Parse a single thread from TOML table *)
let parse_thread_def (tid, val_toml) =
  match val_toml with
  | Otoml.TomlTable k ->
      (match List.assoc_opt "code" k with
       | Some (Otoml.TomlString code) ->
           let reset_regs = extract_reset_regs k in
           Some { tid; code; reset_regs }
       | _ -> None)
  | _ -> None

(** Parse thread definitions from TOML *)
let parse_threads toml =
  match get_table_opt toml ["thread"] with
  | Some thread_list ->
      thread_list
      |> List.filter_map parse_thread_def
      |> List.sort (fun a b -> String.compare a.tid b.tid)
  | None -> []

(** Parse a single section from TOML table *)
let parse_section_def (name, val_toml) =
  match val_toml with
  | Otoml.TomlTable k ->
      (match List.assoc_opt "address" k, List.assoc_opt "code" k with
       | Some (Otoml.TomlString addr_s), Some (Otoml.TomlString sec_code) ->
           let sec_addr = Z.of_string addr_s in
           Some { sec_name = name; sec_addr; sec_code }
       | _ -> None)
  | _ -> None

(** Parse section definitions from TOML *)
let parse_sections toml =
  match get_table_opt toml ["section"] with
  | Some section_list -> List.filter_map parse_section_def section_list
  | None -> []

(** Get architecture from TOML (default: AArch64) *)
let get_arch toml =
  match get_string_opt toml ["arch"] with
  | Some s -> s
  | None -> "AArch64"

(** Get test name from TOML *)
let get_name toml =
  match get_string_opt toml ["name"] with
  | Some s -> s
  | None -> "converted"
