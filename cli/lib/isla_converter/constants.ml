(** Shared constants for memory layout.

    4KB granule, 48-bit VA. *)

(** Page size *)
let page_size = 4096
let page_size_z = Z.of_int page_size

(** Memory layout *)
let initial_pa = Z.of_int 0x2000                 (* PA base, after reserved region *)
let initial_code_va = Z.of_string "0x40000000"    (* 1GB *)
let initial_data_va = Z.of_string "0x8000000000"  (* 32GB *)
let constraint_skip = Z.of_int 0x100000           (* 1MB skip on constraint conflict *)
