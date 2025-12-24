(* Supporting functions *)

let list_get i l = List.nth l (Z.to_int i)

let list_set i v l =
  let rec aux i v l =
  match i, l with
  | _, [] -> raise (Invalid_argument "list_set out of bounds")
  | 0, _ :: tl -> v :: tl
  | n, hd :: tl -> hd :: aux (n - 1) v tl
  in aux (Z.to_int i) v l

let list_last l = List.hd (List.rev l)

let fin_case f0 fS n =
  if Big_int_Z.sign_big_int n > 0 then
    fS (Big_int_Z.pred_big_int n)
  else
    f0 ()

let fin0_magic _ = raise (Failure "Got a value of type fin 0")
