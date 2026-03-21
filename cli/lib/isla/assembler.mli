
val assemble : string -> Bytes.t * (string * int) list
(** Assemble code into a machine code byte sequence and a label map.
    Uses configuration to determine the toolchain. *)
