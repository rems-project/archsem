(** Boolean assertion parser for isla litmus tests.

    Parses expressions like:
    - "1:X0 = 1"               register equality
    - "*x = 2"                 memory equality
    - "1:X0 = 1 & *x = 2"      conjunction
    - "~(1:X0 = 1)"            negation

    Converts to DNF and emits Litmus.Spec.final_cond list with
    both register and memory conditions. *)

open Archsem
open Ast

module Spec = Litmus.Spec

(** {1 Parsing} *)

let parse_string s =
  let lexbuf = Lexing.from_string s in
  try Parser.expr_eof Lexer.token lexbuf
  with
  | Parser.Error ->
    failwith (Printf.sprintf
      "assertion parse error at position %d in: %s"
      lexbuf.lex_curr_p.pos_cnum s)

(** {1 Register normalization} *)

(** Normalize register name: X0 -> R0, W0 -> R0.
    TODO: This loses the W/X width distinction. W registers are 32-bit
    views of 64-bit X registers. Handle properly when adding x86 support
    or when the model gains width-aware register types. *)
let normalize_reg r =
  if String.length r > 0 && (r.[0] = 'X' || r.[0] = 'W') then
    "R" ^ String.sub r 1 (String.length r - 1)
  else r

(** {1 DNF conversion} *)

let rec negate = function
  | Atom (RegEq (t,r,v)) -> Atom (RegNe (t,r,v))
  | Atom (RegNe (t,r,v)) -> Atom (RegEq (t,r,v))
  | Atom (MemEq (s,v)) -> Atom (MemNe (s,v))
  | Atom (MemNe (s,v)) -> Atom (MemEq (s,v))
  | And (a, b) -> Or (negate a, negate b)
  | Or (a, b) -> And (negate a, negate b)
  | Not e -> e
  | True -> True

let rec to_dnf = function
  | Atom a -> [[a]]
  | True -> [[]]
  | Not e -> to_dnf (negate e)
  | Or (a, b) -> to_dnf a @ to_dnf b
  | And (a, b) ->
    let da = to_dnf a and db = to_dnf b in
    List.concat_map (fun ca -> List.map (fun cb -> ca @ cb) db) da

(** {1 Conversion to Litmus.Spec.final_cond} *)

let reg_of_name name =
  match Reg.of_string name with
  | Some r -> r
  | None -> failwith ("assertion: unrecognized register name: " ^ name)

let atoms_to_conds syms atoms =
  let resolve_sym s =
    match Symbols.resolve syms s with
    | Some a -> a
    | None -> failwith ("assertion: unknown symbol: " ^ s)
  in
  let reg_atoms = List.filter_map (function
    | RegEq (t,r,v) -> Some (t, normalize_reg r, Spec.ReqEq (RegVal.Number v))
    | RegNe (t,r,v) -> Some (t, normalize_reg r, Spec.ReqNe (RegVal.Number v))
    | _ -> None) atoms in
  let mem_atoms = List.filter_map (function
    | MemEq (s,v) ->
      Some { Spec.sym = s; addr = resolve_sym s;
             size = Litmus.Config.default_mem_size ();
             req = Spec.MemEq v }
    | MemNe (s,v) ->
      Some { Spec.sym = s; addr = resolve_sym s;
             size = Litmus.Config.default_mem_size ();
             req = Spec.MemNe v }
    | _ -> None) atoms in
  let tids = List.sort_uniq compare (List.map (fun (t,_,_) -> t) reg_atoms) in
  let thread_conds = List.map (fun tid ->
    let reqs = List.filter_map (fun (t,r,req) ->
      if t = tid then Some (reg_of_name r, req) else None) reg_atoms in
    (tid, reqs)
  ) tids in
  (thread_conds, mem_atoms)

(** Parse an assertion string and convert to final_cond list.

    - expect="sat", assertion A     -> each DNF disjunct is Observable
    - expect="sat", assertion ~A    -> inner disjuncts are Unobservable
    - expect="unsat", assertion A   -> each DNF disjunct is Unobservable *)
let to_final_conds ~expect ~syms assertion_str =
  if String.trim assertion_str = "true" || String.trim assertion_str = "" then
    []
  else
    let expr = parse_string assertion_str in
    let is_negated, inner = match expr with
      | Not e -> (true, e) | e -> (false, e) in
    let is_observable =
      (expect = "sat" && not is_negated) ||
      (expect <> "sat" && is_negated) in
    let dnf = to_dnf inner in
    List.filter_map (fun conj ->
      if conj = [] then None
      else
        let thread_conds, mem_conds = atoms_to_conds syms conj in
        if thread_conds = [] && mem_conds = [] then None
        else Some (
          if is_observable
          then Spec.Observable (thread_conds, mem_conds)
          else Spec.Unobservable (thread_conds, mem_conds))
    ) dnf
