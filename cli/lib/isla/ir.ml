(** Parse isla-format TOML into an intermediate representation. *)

type thread = {
  tid : int;
  code : string;
  init : (string * Value_expr.t) list;
}

type section = {
  sec_name : string;
  address : int;
  code : string;
}

type expect =
  | Sat
  | Unsat

type t = {
  arch : Litmus.Arch_id.t;
  name : string;
  threads : thread list;
  sections : section list;
  symbolic : string list;
  locations : (string * Value_expr.t) list;
  expect : expect;
  assertion : Assertion.expr;
}

let type_error fmt = Printf.ksprintf (fun s -> raise (Otoml.Type_error s)) fmt

let parse_value = function
  | Otoml.TomlInteger i -> Value_expr.Const (Z.of_int i)
  | Otoml.TomlString s ->
    (try Const (Z.of_string s) with Invalid_argument _ -> LocVal (Mem s))
  | value ->
    type_error "Value is invalid, should be int or string, but is: %s"
      (Otoml.Printer.to_string value)

let parse_value_expr_string s =
  let lexbuf = Lexing.from_string s in
  try Parser.final_value_expr Lexer.token lexbuf
  with Parser.Error ->
    type_error "value expression parse error at position %d in: %s"
      lexbuf.lex_curr_p.pos_cnum s

let parse_reset_value = function
  | Otoml.TomlInteger i -> Value_expr.Const (Z.of_int i)
  | Otoml.TomlString s ->
    (try Value_expr.Const (Z.of_string s)
     with Invalid_argument _ ->
       let expr = parse_value_expr_string s in
       Const (Value_expr.eval expr))
  | value ->
    type_error "reset value is invalid, should be int or string expression, but is: %s"
      (Otoml.Printer.to_string value)

let parse_thread (tid, table) =
  let tid =
    match int_of_string_opt tid with
    | Some tid -> tid
    | None -> type_error "Thread table contained a non-number field: %s" tid
  in
  let _ = Otoml.get_table table in
  let code = Otoml.find table Otoml.get_string ["code"] |> String.trim in
  let init = Otoml.find_or ~default:[] table (Otoml.get_table_values parse_value) ["init"] in
  let reset = Otoml.find_or ~default:[] table (Otoml.get_table_values parse_reset_value) ["reset"] in
  let has_init name = List.exists (fun (k, _) -> k = name) init in
  let merged = init @ List.filter (fun (k, _) -> not (has_init k)) reset in
  { tid; code; init = merged }

let parse_threads toml =
  let table = Otoml.get_table toml in
  List.sort (fun a b -> compare a.tid b.tid) (List.map parse_thread table)

let parse_address = function
  | Otoml.TomlInteger i -> i
  | Otoml.TomlString s ->
    (try Z.to_int (Z.of_string s)
     with Invalid_argument _ ->
       raise (Otoml.Type_error ("invalid address: " ^ s)))
  | v ->
    raise (Otoml.Type_error
      ("address must be integer or hex string, got: " ^
       Otoml.Printer.to_string v))

let parse_section (name, table) =
  let _ = Otoml.get_table table in
  let address = Otoml.find table parse_address ["address"] in
  let code = Otoml.find table Otoml.get_string ["code"] |> String.trim in
  { sec_name = name; address; code }

let parse_sections toml =
  let table = Otoml.get_table toml in
  List.map parse_section table

let parse_expect toml =
  match Otoml.get_string toml with
  | "sat" -> Sat
  | "unsat" -> Unsat
  | expect ->
    raise (Otoml.Type_error ("invalid expectation value: " ^ expect))

let parse_assertion_expr s =
  let lexbuf = Lexing.from_string s in
  try Parser.final_expr Lexer.token lexbuf
  with Parser.Error ->
    type_error
         "assertion parse error at position %d in: %s"
         lexbuf.lex_curr_p.pos_cnum s

let parse_assertion toml =
  let assertion_str = Otoml.get_string toml |> String.trim in
  if assertion_str = "" then
    Assertion.True
  else
    parse_assertion_expr assertion_str

let parse_arch toml =
  let arch_string = Otoml.get_string toml in
  try Litmus.Arch_id.of_string arch_string
  with Failure msg -> raise (Otoml.Type_error msg)

let of_toml toml =
  {
    arch = Otoml.find toml parse_arch ["arch"];
    name = Otoml.find_or ~default:"unknown" toml Otoml.get_string ["name"];
    threads = Otoml.find toml parse_threads ["thread"];
    sections =
      Otoml.find_or ~default:[] toml parse_sections ["section"];
    symbolic =
      Otoml.find_or ~default:[] toml (Otoml.get_array Otoml.get_string) ["symbolic"];
    locations = Otoml.find_or ~default:[] toml (Otoml.get_table_values parse_value) ["locations"];
    expect = Otoml.find_or ~default:Sat toml parse_expect ["final"; "expect"];
    assertion =
      Otoml.find_or ~default:Assertion.True toml parse_assertion ["final"; "assertion"]
  }
