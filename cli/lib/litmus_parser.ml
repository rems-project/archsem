(** Litmus test TOML parser.

    Parses TOML files describing litmus tests with the following structure:
    - [[registers]]: Initial register state per thread
    - [[memory]]: Initial memory contents
    - [[termCond]]: Termination conditions per thread (typically PC values)
    - [[outcome]]: Expected observable/unobservable outcomes *)

(** {1 Types} *)

type gen = Archsem.RegVal.gen =
  | Number of Z.t
  | String of string
  | Array of gen list
  | Struct of (string * gen) list

type requirement =
  | Eq of gen
  | Neq of gen

(** A condition maps thread IDs to lists of (register_name, requirement). *)
type cond = (int * (string * requirement) list) list

type outcome =
  | Observable of cond
  | Unobservable of cond

type mem_block = {
  base : int;
  size : int;
  step : int option;
  data : [ `Single of int | `Array of int list ];
}

type parsed_test = {
  fuel : int;
  threads : (string * gen) list list;
  memory : mem_block list;
  term_conds : (string * requirement) list list;
  outcomes : outcome list;
}

(** {1 TOML Helpers} *)

let get_int = function
  | Otoml.TomlInteger i -> i
  | _ -> failwith "Expected integer"

let get_list = function
  | Otoml.TomlArray l | Otoml.TomlTableArray l -> l
  | _ -> failwith "Expected list"

let get_pairs = function
  | Otoml.TomlTable pairs | Otoml.TomlInlineTable pairs -> pairs
  | _ -> failwith "Expected table"

(** {1 Value Parsing} *)

let rec parse_value = function
  | Otoml.TomlInteger i -> Number (Z.of_int i)
  | Otoml.TomlString s -> String s
  | Otoml.TomlTable t | Otoml.TomlInlineTable t ->
    Struct (List.map (fun (k, v) -> (k, parse_value v)) t)
  | _ -> failwith "Unsupported value type"

let parse_requirement toml =
  match toml with
  | Otoml.TomlTable pairs | Otoml.TomlInlineTable pairs ->
    (match List.assoc_opt "op" pairs, List.assoc_opt "val" pairs with
     | Some (Otoml.TomlString "eq"), Some v -> Eq (parse_value v)
     | Some (Otoml.TomlString "ne"), Some v -> Neq (parse_value v)
     | Some (Otoml.TomlString op), _ -> failwith ("Unknown op: " ^ op)
     | _ -> Eq (parse_value toml))
  | _ -> Eq (parse_value toml)

(** Parse a table of register assignments into [(name, requirement)] pairs.
    All register names are kept as strings — model-specific resolution
    happens in the runner. *)
let parse_reg_table toml =
  get_pairs toml |> List.map (fun (k, v) -> (k, parse_requirement v))

(** {1 Section Parsing} *)

let parse_threads toml =
  Otoml.find toml get_list ["registers"]
  |> List.map (fun t ->
       get_pairs t |> List.map (fun (k, v) ->
         (k, parse_value v)))

let parse_memory toml =
  Otoml.find toml get_list ["memory"]
  |> List.filter_map (fun table ->
       match table with
       | Otoml.TomlTable _ ->
         let base = Otoml.find table get_int ["base"] in
         let size = Otoml.find table get_int ["size"] in
         let step = Otoml.find_opt table get_int ["step"] in
         let data = match Otoml.find table (fun x -> x) ["data"] with
           | Otoml.TomlArray data_list ->
             `Array (List.map get_int data_list)
           | Otoml.TomlInteger v -> `Single v
           | _ -> failwith "Invalid memory data format"
         in
         Some { base; size; step; data }
       | _ -> None)

let parse_term_conds toml =
  Otoml.find toml get_list ["termCond"]
  |> List.map parse_reg_table

(** {1 Outcome Parsing} *)

let parse_cond toml =
  get_pairs toml |> List.filter_map (fun (tid_str, regs) ->
    match int_of_string_opt tid_str with
    | None -> failwith ("Invalid thread ID: " ^ tid_str)
    | Some tid -> Some (tid, parse_reg_table regs))

let parse_outcomes toml =
  Otoml.find toml get_list ["outcome"] |> List.filter_map (fun node ->
    match node with
    | Otoml.TomlTable pairs | Otoml.TomlInlineTable pairs ->
      (match List.assoc_opt "observable" pairs, List.assoc_opt "unobservable" pairs with
       | Some v, None -> Some (Observable (parse_cond v))
       | None, Some v -> Some (Unobservable (parse_cond v))
       | Some _, Some _ -> failwith "Cannot have both observable and unobservable"
       | None, None -> failwith "Outcome must have observable or unobservable")
    | _ -> None)

(** {1 Entry Point} *)

let parse_file filename =
  let toml = Otoml.Parser.from_file filename in
  let fuel = Otoml.find_opt toml get_int ["fuel"]
    |> Option.value ~default:1000 in
  let threads = parse_threads toml in
  let memory = parse_memory toml in
  let term_conds = parse_term_conds toml in
  let outcomes = parse_outcomes toml in
  let num_threads = List.length threads in
  if List.length term_conds <> num_threads then
    failwith "termCond count must match thread count";
  { fuel; threads; memory; term_conds; outcomes }
