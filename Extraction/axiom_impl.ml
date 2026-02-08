(* Implementations of classical axioms required by the extraction.
   These axioms are used by Coq's real number library but should not
   be called during memory model execution. We provide bounded-search
   implementations as a fallback. *)

(* sig_forall_dec: decides if a predicate holds for all natural numbers.
   Returns None if true for all n, Some n if there's a counterexample. *)
let sig_forall_dec (p : Big_int_Z.big_int -> bool) : Big_int_Z.big_int option =
  let rec search n limit =
    if n >= limit then None
    else if not (p (Big_int_Z.big_int_of_int n)) then
      Some (Big_int_Z.big_int_of_int n)
    else
      search (n + 1) limit
  in search 0 10000

(* sig_not_dec: The Coq axiom `forall P : Prop, { ~~P } + { ~P }` is
   specialized to a specific P during extraction. The result is just a bool.
   We return true (corresponding to the ~~P branch) as a reasonable default. *)
let sig_not_dec : bool = true
