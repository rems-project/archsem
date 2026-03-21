(** Boolean expression language for isla litmus test assertions. *)

type op = Eq | Ne

type atom = Cmp of Term.t * op * Term.t

type expr =
  | Atom of atom
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | True
  | False

let negate_op = function
  | Eq -> Ne
  | Ne -> Eq

let negate_atom (Cmp (lhs, op, rhs)) = Cmp (lhs, negate_op op, rhs)

let rec negate = function
  | Atom atom -> Atom (negate_atom atom)
  | And (a, b) -> Or (negate a, negate b)
  | Or (a, b) -> And (negate a, negate b)
  | Not e -> e
  | True -> False
  | False -> True

let rec to_dnf = function
  | Atom a -> [[a]]
  | True -> [[]]
  | False -> []
  | Not e -> to_dnf (negate e)
  | Or (a, b) -> to_dnf a @ to_dnf b
  | And (a, b) ->
    let da = to_dnf a and db = to_dnf b in
    (* Take the cartesian product of da and db to enumerate all the clauses *)
    List.concat_map (fun ca -> List.map (fun cb -> ca @ cb) db) da
