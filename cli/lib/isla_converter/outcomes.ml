(** Boolean expression parser for litmus test assertions.

    Handles expressions like:
    - "1:X0 = 0"                          (register equality)
    - "*x = 2"                            (memory equality)
    - "1:X0 = 0 & *x = 1"                 (conjunction)
    - "1:X0 = 0 | 1:X0 = 1"               (disjunction)
    - "~(1:X0 = 0)"                       (negation)
    - "~((1:X0 = 0 & *x = 2) | ...)"      (complex nested)
*)

(** Atomic condition types *)
type atom =
  | RegEq of string * string * int    (* tid, reg, value - equality *)
  | RegNe of string * string * int    (* tid, reg, value - inequality *)
  | MemEq of string * int             (* symbol, value - equality *)
  | MemNe of string * int             (* symbol, value - inequality *)

(** Boolean expression AST *)
type expr =
  | Atom of atom
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | True
  | False

(** Token types for lexer *)
type token =
  | LPAREN | RPAREN
  | AND | OR | NOT
  | EQ | NE
  | COLON | STAR | COMMA
  | NUM of int
  | IDENT of string
  | EOF

(** Lexer: convert string to token list *)
let tokenize s =
  let len = String.length s in
  let pos = ref 0 in
  let tokens = ref [] in

  let peek () = if !pos < len then Some s.[!pos] else None in
  let advance () = incr pos in
  let skip_whitespace () =
    while !pos < len && (s.[!pos] = ' ' || s.[!pos] = '\t' || s.[!pos] = '\n') do
      advance ()
    done
  in

  while !pos < len do
    skip_whitespace ();
    match peek () with
    | None -> ()
    | Some c ->
      (match c with
       | '(' -> tokens := LPAREN :: !tokens; advance ()
       | ')' -> tokens := RPAREN :: !tokens; advance ()
       | '&' -> tokens := AND :: !tokens; advance ()
       | '|' -> tokens := OR :: !tokens; advance ()
       | '~' -> tokens := NOT :: !tokens; advance ()
       | '=' -> tokens := EQ :: !tokens; advance ()
       | '*' -> tokens := STAR :: !tokens; advance ()
       | ':' -> tokens := COLON :: !tokens; advance ()
       | ',' -> tokens := COMMA :: !tokens; advance ()
       | '0'..'9' ->
         let start = !pos in
         while !pos < len && s.[!pos] >= '0' && s.[!pos] <= '9' do
           advance ()
         done;
         let num_str = String.sub s start (!pos - start) in
         tokens := NUM (int_of_string num_str) :: !tokens
       | 'a'..'z' | 'A'..'Z' | '_' ->
         let start = !pos in
         while !pos < len &&
               (let c = s.[!pos] in
                (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
                (c >= '0' && c <= '9') || c = '_') do
           advance ()
         done;
         let ident = String.sub s start (!pos - start) in
         tokens := IDENT ident :: !tokens
       | _ -> advance ()  (* skip unknown chars *)
      )
  done;
  List.rev (EOF :: !tokens)

(** Parser state *)
type parser_state = {
  mutable tokens: token list;
}

let make_parser tokens = { tokens }

let current p = match p.tokens with t :: _ -> t | [] -> EOF
let advance p = match p.tokens with _ :: rest -> p.tokens <- rest | [] -> ()
let expect p tok =
  if current p = tok then advance p
  else failwith (Printf.sprintf "Expected token, got something else")

(** Parse a value expression: either a number or a function call like desc3(z, page_table_base).
    Returns the evaluated integer value. *)
let rec parse_value_expr p =
  match current p with
  | NUM v -> advance p; v
  | IDENT name ->
    advance p;
    (match current p with
     | LPAREN ->
       (* Function call: name(arg1, arg2, ...) *)
       advance p;
       let args = parse_func_args p in
       expect p RPAREN;
       (* Build expression string and evaluate using DSL evaluator *)
       let args_str = String.concat ", " args in
       let expr_str = Printf.sprintf "%s(%s)" name args_str in
       let expr = Evaluator.parse_expr expr_str in
       Z.to_int (Evaluator.eval expr)
     | _ ->
       (* Simple variable reference - evaluate it *)
       let expr = Evaluator.parse_expr name in
       Z.to_int (Evaluator.eval expr))
  | _ -> failwith "Expected numeric value or expression"

and parse_func_args p =
  (* Parse a single argument, which may be a nested function call *)
  let parse_single_arg () =
    let buf = Buffer.create 32 in
    let rec collect depth =
      match current p with
      | RPAREN when depth = 0 -> Buffer.contents buf
      | COMMA when depth = 0 -> Buffer.contents buf
      | RPAREN -> Buffer.add_char buf ')'; advance p; collect (depth - 1)
      | LPAREN -> Buffer.add_char buf '('; advance p; collect (depth + 1)
      | NUM v -> Buffer.add_string buf (string_of_int v); advance p; collect depth
      | IDENT name -> Buffer.add_string buf name; advance p; collect depth
      | EQ -> Buffer.add_char buf '='; advance p; collect depth
      | COMMA when depth > 0 -> Buffer.add_string buf ", "; advance p; collect depth
      | _ -> Buffer.contents buf
    in
    collect 0
  in
  let rec loop acc =
    match current p with
    | RPAREN -> List.rev acc
    | COMMA -> advance p; loop acc
    | EOF -> List.rev acc
    | _ ->
        let arg = parse_single_arg () in
        if arg = "" then List.rev acc
        else loop (arg :: acc)
  in
  loop []

(** Recursive descent parser for boolean expressions

    Grammar:
      expr     -> or_expr
      or_expr  -> and_expr ('|' and_expr)*
      and_expr -> unary ('&' unary)*
      unary    -> '~' unary | primary
      primary  -> '(' expr ')' | atom
      atom     -> NUM ':' IDENT '=' NUM     (register eq)
               |  NUM ':' IDENT '~' NUM     (register ne) - not standard but handle
               |  '*' IDENT '=' NUM         (memory eq)
               |  '*' IDENT '~' NUM         (memory ne)
*)

let rec parse_expr p = parse_or_expr p

and parse_or_expr p =
  let left = parse_and_expr p in
  let rec loop left =
    match current p with
    | OR -> advance p; loop (Or (left, parse_and_expr p))
    | _ -> left
  in
  loop left

and parse_and_expr p =
  let left = parse_unary p in
  let rec loop left =
    match current p with
    | AND -> advance p; loop (And (left, parse_unary p))
    | _ -> left
  in
  loop left

and parse_unary p =
  match current p with
  | NOT -> advance p; Not (parse_unary p)
  | _ -> parse_primary p

and parse_primary p =
  match current p with
  | LPAREN ->
    advance p;
    let e = parse_expr p in
    expect p RPAREN;
    e
  | NUM tid_num ->
    (* Register assertion: NUM:IDENT = NUM *)
    advance p;
    expect p COLON;
    let reg = match current p with
      | IDENT r -> advance p; r
      | _ -> failwith "Expected register name"
    in
    let is_eq = match current p with
      | EQ -> advance p; true
      | NOT -> advance p; false  (* ~ used as != *)
      | _ -> failwith "Expected = or ~"
    in
    let value = parse_value_expr p in
    let tid = string_of_int tid_num in
    (* Normalize register name: X0 -> R0 *)
    let reg = if String.length reg > 0 && reg.[0] = 'X' then
      "R" ^ String.sub reg 1 (String.length reg - 1)
    else reg in
    if is_eq then Atom (RegEq (tid, reg, value))
    else Atom (RegNe (tid, reg, value))
  | STAR ->
    (* Memory assertion: *IDENT = NUM *)
    advance p;
    let sym = match current p with
      | IDENT s -> advance p; s
      | _ -> failwith "Expected symbol name"
    in
    let is_eq = match current p with
      | EQ -> advance p; true
      | NOT -> advance p; false
      | _ -> failwith "Expected = or ~"
    in
    let value = parse_value_expr p in
    if is_eq then Atom (MemEq (sym, value))
    else Atom (MemNe (sym, value))
  | IDENT "true" ->
    advance p;
    True
  | IDENT "false" ->
    advance p;
    False
  | _ ->
    (* Unknown - skip and return True as placeholder *)
    advance p;
    True

(** Parse assertion string into expression AST *)
let parse assertion =
  let tokens = tokenize assertion in
  let p = make_parser tokens in
  parse_expr p

(** Negate an expression (push negation inward using De Morgan's laws) *)
let rec negate = function
  | Atom (RegEq (t, r, v)) -> Atom (RegNe (t, r, v))
  | Atom (RegNe (t, r, v)) -> Atom (RegEq (t, r, v))
  | Atom (MemEq (s, v)) -> Atom (MemNe (s, v))
  | Atom (MemNe (s, v)) -> Atom (MemEq (s, v))
  | And (a, b) -> Or (negate a, negate b)
  | Or (a, b) -> And (negate a, negate b)
  | Not e -> e  (* double negation elimination *)
  | True -> False
  | False -> True

(** Simplify expression (remove double negations, flatten) *)
let rec simplify = function
  | Not (Not e) -> simplify e
  | Not e -> Not (simplify e)
  | And (a, b) -> And (simplify a, simplify b)
  | Or (a, b) -> Or (simplify a, simplify b)
  | e -> e

(** Convert expression to Disjunctive Normal Form (DNF).
    Result is a list of conjunctions (each conjunction is a list of atoms).
    This represents: (a1 & a2 & ...) | (b1 & b2 & ...) | ... *)
let rec to_dnf expr =
  let expr = simplify expr in
  match expr with
  | Atom a -> [[a]]
  | True -> [[]]  (* empty conjunction = true *)
  | False -> []   (* empty disjunction = false *)
  | Not e ->
    (* Push negation to atoms *)
    to_dnf (negate e)
  | And (a, b) ->
    (* Distribute: (A1|A2) & (B1|B2) = (A1&B1)|(A1&B2)|(A2&B1)|(A2&B2) *)
    let dnf_a = to_dnf a in
    let dnf_b = to_dnf b in
    List.concat_map (fun conj_a ->
      List.map (fun conj_b -> conj_a @ conj_b) dnf_b
    ) dnf_a
  | Or (a, b) ->
    (* Simply concatenate disjuncts *)
    to_dnf a @ to_dnf b

(** Check if a conjunction contains contradictions (e.g., X=0 & X=1) *)
let has_contradiction conj =
  let reg_eqs = List.filter_map (function RegEq (t,r,v) -> Some (t,r,v,true) | RegNe (t,r,v) -> Some (t,r,v,false) | _ -> None) conj in
  let mem_eqs = List.filter_map (function MemEq (s,v) -> Some (s,v,true) | MemNe (s,v) -> Some (s,v,false) | _ -> None) conj in
  (* Check for reg contradictions: same tid:reg with different values for eq, or eq and ne with same value *)
  let rec check_reg = function
    | [] -> false
    | (t1,r1,v1,is_eq1) :: rest ->
      if List.exists (fun (t2,r2,v2,is_eq2) ->
        t1 = t2 && r1 = r2 &&
        ((is_eq1 && is_eq2 && v1 <> v2) ||  (* X=0 & X=1 *)
         (is_eq1 && not is_eq2 && v1 = v2) ||  (* X=0 & X!=0 *)
         (not is_eq1 && is_eq2 && v1 = v2))    (* X!=0 & X=0 *)
      ) rest then true
      else check_reg rest
  in
  let rec check_mem = function
    | [] -> false
    | (s1,v1,is_eq1) :: rest ->
      if List.exists (fun (s2,v2,is_eq2) ->
        s1 = s2 &&
        ((is_eq1 && is_eq2 && v1 <> v2) ||
         (is_eq1 && not is_eq2 && v1 = v2) ||
         (not is_eq1 && is_eq2 && v1 = v2))
      ) rest then true
      else check_mem rest
  in
  check_reg reg_eqs || check_mem mem_eqs

(** Remove contradictory conjunctions from DNF *)
let remove_contradictions dnf =
  List.filter (fun conj -> not (has_contradiction conj)) dnf

(** Convert DNF to outcome format.
    Returns list of (is_forbidden, reg_asserts, mem_asserts) *)
type outcome = {
  reg_asserts: (string * string * int * bool) list;  (* tid, reg, value, is_eq *)
  mem_asserts: (string * int * bool) list;           (* symbol, value, is_eq *)
}

let dnf_to_outcomes dnf =
  List.filter_map (fun conj ->
    if conj = [] then None  (* skip empty/true conjunctions *)
    else
      let reg_asserts = List.filter_map (function
        | RegEq (t, r, v) -> Some (t, r, v, true)
        | RegNe (t, r, v) -> Some (t, r, v, false)
        | _ -> None
      ) conj in
      let mem_asserts = List.filter_map (function
        | MemEq (s, v) -> Some (s, v, true)
        | MemNe (s, v) -> Some (s, v, false)
        | _ -> None
      ) conj in
      Some { reg_asserts; mem_asserts }
  ) dnf

(** Check if expression is a top-level negation *)
let is_top_negation = function
  | Not _ -> true
  | _ -> false

(** Strip top-level negation *)
let strip_negation = function
  | Not e -> e
  | e -> e

(** Main entry point: parse assertion and convert to outcomes.

    Parameters:
    - assertion: the assertion string
    - expect_sat: true if expect="sat", false if expect="unsat"

    Returns: (is_allowed, outcomes) where is_allowed indicates if these
    outcomes should be marked as "allowed" or "forbidden"

    Semantics:
    - expect=sat with assertion A: we expect A to be satisfiable (allowed)
    - expect=sat with assertion ~X: we expect ~X to be satisfiable,
      so X should be "forbidden" (at least one execution should avoid X)
    - expect=unsat with assertion A: A should not be satisfiable (forbidden)
*)
let parse_assertion assertion expect_sat =
  try
    let expr = parse assertion in

    (* Check for top-level negation *)
    let (is_negated, inner_expr) =
      if is_top_negation expr then (true, strip_negation expr)
      else (false, expr)
    in

    (* Determine if outcomes should be allowed or forbidden:
       - expect=sat, not negated -> allowed (we want to see these)
       - expect=sat, negated -> forbidden (we want to avoid these)
       - expect=unsat, not negated -> forbidden
       - expect=unsat, negated -> allowed *)
    let is_allowed = (expect_sat && not is_negated) || (not expect_sat && is_negated) in

    (* Convert the inner expression to DNF (without negation) *)
    let dnf = to_dnf inner_expr in
    let dnf = remove_contradictions dnf in
    let outcomes = dnf_to_outcomes dnf in
    (is_allowed, outcomes)
  with e ->
    Printf.eprintf "Warning: Failed to parse assertion '%s': %s\n"
      assertion (Printexc.to_string e);
    (true, [])  (* Default to allowed with no constraints *)
