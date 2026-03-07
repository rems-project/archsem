type empty = |

let lengthZ l = Z.of_int (List.length l)

(** Code for Rocq's BinaryString.Raw.to_N *)
let bin_str_to_N s z = Z.((z lsl String.length s) lor of_string_base 2 s)

let hex_str_to_N s z =
  Z.((z lsl Stdlib.(4 * String.length s)) lor of_string_base 16 s)

let hex_str_of_Z z = Z.format "#x" z
