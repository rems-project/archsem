(* Supporting functions *)

let list_get i l = List.nth l (Z.to_int i)

let list_set i v l =
  let rec aux i v l =
  match i, l with
  | _, [] -> raise (Invalid_argument "list_set out of bounds")
  | 0, _ :: tl -> v :: tl
  | n, hd :: tl -> hd :: aux (n - 1) v tl
  in aux (Z.to_int i) v l

let rec list_last l =
  match l with
  | [] -> raise (Invalid_argument "list_last on empty list")
  | [x] -> x
  | _ :: tl -> list_last tl

let fin_case f0 fS n =
  if Z.sign n > 0 then
    fS (Z.pred n)
  else
    f0 ()

let fin0_magic _ = raise (Failure "Got a value of type fin 0")

let vec_eqdep_dec eq_dec _ _ v1 v2 = List.equal eq_dec v1 v2
