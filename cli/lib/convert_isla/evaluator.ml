open Ast

(* --- Expression Evaluator (Parsed) --- *)

let parse_string s =
  let lexbuf = Lexing.from_string s in
  try Parser.main_expr Lexer.read lexbuf
  with _ ->
     failwith ("Failed to parse expression: " ^ s)

let rec eval e =
  match e with
  | EInt i -> i
  | EVar v -> Symbols.get_symbol_addr v
  | ESlice(sub, hi, lo) ->
       let v = eval sub in
       let mask = Z.sub (Z.shift_left Z.one (hi - lo + 1)) Z.one in
       Z.logand (Z.shift_right v lo) mask
  | ECall("extz", args) -> snd(List.nth args 0) |> eval
  | ECall("mkdesc2", args) -> let t = eval(snd(List.nth args 0)) in Z.logor t (Z.of_int 3)
  | ECall("mkdesc3", args) -> let oa = eval(snd(List.nth args 0)) in Z.logor oa (Z.of_int 3)
  | ECall ("pte1", args) ->
     let va = eval (snd (List.nth args 0)) in
     let table =
       if List.length args > 1 then eval(snd(List.nth args 1))
       else Symbols.get_symbol_addr "page_table_base"
     in
     let idx = Z.to_int (Z.logand (Z.shift_right va 30) (Z.of_int 0x1FF)) in
     Z.add table (Z.of_int (idx * 8))
  | ECall ("pte2", args) ->
     let va = eval (snd (List.nth args 0)) in
     let table =
       if List.length args > 1 then eval(snd(List.nth args 1))
       else Symbols.get_symbol_addr "page_table_base"
     in
     let idx = Z.to_int (Z.logand (Z.shift_right va 21) (Z.of_int 0x1FF)) in
     Z.add table (Z.of_int (idx * 8))
  | ECall ("pte3", args) ->
     let va = eval (snd (List.nth args 0)) in
     let table =
       if List.length args > 1 then eval(snd(List.nth args 1))
       else Symbols.get_symbol_addr "page_table_base"
     in
     let idx = Z.to_int (Z.logand (Z.shift_right va 12) (Z.of_int 0x1FF)) in
     Z.add table (Z.of_int (idx * 8))
  | ECall("bvor", args) -> Z.logor (eval(snd(List.nth args 0))) (eval(snd(List.nth args 1)))
  | ECall("bvlshr", args) -> Z.shift_right (eval(snd(List.nth args 0))) (Z.to_int (eval(snd(List.nth args 1))))
  | ECall("table3", args) -> eval (snd (List.nth args 0))
  | ECall("page", args) -> Z.logand (eval(snd(List.nth args 0))) (Z.of_string "0xFFFFFFFFFFFFF000")
  | ECall("offset", args) ->
     let va_arg = try List.assoc "va" args with _ -> snd(List.nth args 1) in
     let va = eval va_arg in
     let idx = Z.to_int (Z.logand (Z.shift_right va 12) (Z.of_int 0x1FF)) in
     Z.of_int (idx*8)
  | ECall("ttbr", args) ->
       let base_arg = try List.assoc "base" args with _ -> snd(List.nth args 1) in
       let base = eval base_arg in
       base
  | ECall("add_bits_int", [( _, sub); (_, EInt delta)]) -> Z.add (eval sub) delta
  | ECall _ -> Z.zero
