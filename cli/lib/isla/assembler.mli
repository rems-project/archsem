(** Assemble code into a machine code byte sequence
    use configuration to figure out the toolchain *)
val assemble : string -> Bytes.t
