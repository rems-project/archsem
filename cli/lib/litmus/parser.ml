(** Litmus test TOML parser.

    Parses TOML files describing litmus tests:
    - [[registers]]: Initial register state per thread
    - [[memory]]: Initial memory contents
    - [[termCond]]: Termination conditions per thread (typically PC values)
    - [[outcome]]: Expected observable/unobservable final

    Parsing path: TOML -> Spec.t *)

open Archsem

(** {1 TOML Helpers} *)

let toml_type_name = function
  | Otoml.TomlInteger _ -> "integer"
  | Otoml.TomlFloat _ -> "float"
  | Otoml.TomlString _ -> "string"
  | Otoml.TomlBoolean _ -> "boolean"
  | Otoml.TomlArray _ -> "array"
  | Otoml.TomlTable _ -> "table"
  | Otoml.TomlInlineTable _ -> "inline table"
  | Otoml.TomlTableArray _ -> "table array"
  | _ -> "unknown"

let get_int = function
  | Otoml.TomlInteger i -> i
  | v -> failwith ("expected integer, got " ^ toml_type_name v)

let get_string = function
  | Otoml.TomlString s -> s
  | v -> failwith ("expected string, got " ^ toml_type_name v)

let get_list = function
  | Otoml.TomlArray l | Otoml.TomlTableArray l -> l
  | v -> failwith ("expected array, got " ^ toml_type_name v)

let get_table = function
  | Otoml.TomlTable table | Otoml.TomlInlineTable table -> table
  | v -> failwith ("expected table, got " ^ toml_type_name v)

(** {1 TOML -> Spec.t} *)

(** Convert a TOML value to RegVal.gen *)
let rec toml_to_gen = function
  | Otoml.TomlInteger i -> RegVal.Number (Z.of_int i)
  | Otoml.TomlString s -> RegVal.String s
  | Otoml.TomlArray l -> RegVal.Array (List.map toml_to_gen l)
  | Otoml.TomlTable t | Otoml.TomlInlineTable t ->
    RegVal.Struct (List.map (fun (k, v) -> (k, toml_to_gen v)) t)
  | v -> failwith ("unsupported register value type: " ^ toml_type_name v)

(** Parse [[registers]] into register lists with Reg.t keys *)
let parse_test_registers toml =
  Otoml.find toml get_list ["registers"]
  |> List.map (fun t ->
      get_table t |> List.map (fun (k, v) -> (Reg.of_string_exn k, toml_to_gen v)))

(** Parse [[memory]] into abstract memory blocks *)
let parse_test_memory toml =
  Otoml.find toml get_list ["memory"]
  |> List.filter_map (fun table ->
      match table with
      | Otoml.TomlTable _ ->
        let base = Z.of_int (Otoml.find table get_int ["base"]) in
        let size = Otoml.find table get_int ["size"] in
        let values = match Otoml.find table (fun x -> x) ["data"] with
          | Otoml.TomlArray data_list -> List.map get_int data_list
          | Otoml.TomlInteger v -> [v]
          | v -> failwith ("[[memory]].data: expected integer or array, got " ^ toml_type_name v)
        in
        let n = List.length values in
        let step = Otoml.find_opt table get_int ["step"]
          |> Option.value ~default:(if n > 0 then size / n else size) in
        let data = Bytes.create (n * step) in
        List.iteri (fun i v ->
          for j = 0 to step - 1 do
            Bytes.set data (i * step + j) (Char.chr ((v lsr (j * 8)) land 0xFF))
          done
        ) values;
        let name = Otoml.find_opt table get_string ["name"] in
        let kind = Otoml.find_opt table get_string ["kind"]
          |> Option.map Spec.memory_kind_of_string in
        Some { Spec.base; size; step; data; name; kind }
      | _ -> None)

(** Parse [[termCond]] into term cond lists with Reg.t keys *)
let parse_test_termcond toml =
  Otoml.find toml get_list ["termCond"]
  |> List.map (fun t ->
      get_table t |> List.map (fun (k, v) -> (Reg.of_string_exn k, toml_to_gen v)))

(** Parse a requirement from TOML into Spec.reg_requirement *)
let parse_test_requirement toml =
  match toml with
  | Otoml.TomlTable pairs | Otoml.TomlInlineTable pairs ->
    (match List.assoc_opt "op" pairs, List.assoc_opt "val" pairs with
     | Some (Otoml.TomlString "eq"), Some v -> Spec.ReqEq (toml_to_gen v)
     | Some (Otoml.TomlString "ne"), Some v -> Spec.ReqNe (toml_to_gen v)
     | Some (Otoml.TomlString op), _ -> failwith ("[[outcome]] unknown requirement op: " ^ op)
     | _ -> Spec.ReqEq (toml_to_gen toml))
  | _ -> Spec.ReqEq (toml_to_gen toml)

(** Parse a condition block into thread conditions with Reg.t keys *)
let parse_test_cond toml =
  let pairs = get_table toml in
  let reg_pairs = match List.assoc_opt "regs" pairs with
    | Some regs_table -> get_table regs_table
    | None -> pairs
  in
  reg_pairs |> List.filter_map (fun (tid_str, regs) ->
    match int_of_string_opt tid_str with
    | None -> None
    | Some tid ->
      let reqs = get_table regs
        |> List.map (fun (k, v) -> (Reg.of_string_exn k, parse_test_requirement v)) in
      Some (tid, reqs))

(** Parse all [[outcome]] blocks into final conditions *)
let parse_test_finals toml =
  Otoml.find toml get_list ["outcome"] |> List.filter_map (fun node ->
    match node with
    | Otoml.TomlTable pairs | Otoml.TomlInlineTable pairs ->
      (match List.assoc_opt "observable" pairs, List.assoc_opt "unobservable" pairs with
       | Some v, None -> Some (Spec.Observable (parse_test_cond v))
       | None, Some v -> Some (Spec.Unobservable (parse_test_cond v))
       | Some _, Some _ -> failwith "[[outcome]] cannot have both observable and unobservable"
       | None, None -> failwith "[[outcome]] must have observable or unobservable key")
    | _ -> None)

(** Parse a TOML file into a Spec.t *)
let parse_to_spec toml =
  { Spec.
    arch = Otoml.find toml get_string ["arch"];
    name = Otoml.find toml get_string ["name"];
    registers = parse_test_registers toml;
    memory = parse_test_memory toml;
    term_cond = parse_test_termcond toml;
    finals = parse_test_finals toml;
  }
