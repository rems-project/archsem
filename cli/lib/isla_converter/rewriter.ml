(** Instruction and register rewriter for isla-to-archsem conversion.

    This module handles instruction transformations needed before assembly
    encoding or output emission. It consolidates all rewrites in one place
    for easier maintenance and extension.

    Current rewrites:
    - TLBI: Convert non-shareable variants to inner-shareable (IS)
    - Registers: Normalize X registers to R format (X0 -> R0) *)

(** {1 TLBI Instruction Rewriting}

    The model only supports inner-shareable (IS) TLBI variants.
    For single-core semantics, non-IS and IS variants are equivalent,
    so we rewrite all non-IS TLBI instructions to their IS counterparts. *)

(** TLBI variants that take a register operand (e.g., "TLBI VAE1, X0") *)
let tlbi_with_reg = [
  (* EL1 variants *)
  "VAE1"; "VALE1"; "VAAE1"; "VAALE1"; "ASIDE1";
  (* EL2 variants *)
  "VAE2"; "VALE2"; "IPAS2E1"; "IPAS2LE1";
  (* EL3 variants *)
  "VAE3"; "VALE3";
]

(** TLBI variants without register operand (e.g., "TLBI VMALLE1") *)
let tlbi_no_reg = [
  "VMALLE1"; "VMALLS12E1"; "ALLE1"; "ALLE2"; "ALLE3";
]

(** [rewrite_tlbi_to_is asm_str] rewrites non-shareable TLBI instructions
    to their inner-shareable (IS) equivalents.

    Examples:
    - "TLBI VAE1, X0" -> "TLBI VAE1IS, X0"
    - "TLBI VMALLE1" -> "TLBI VMALLE1IS" *)
let rewrite_tlbi_to_is asm_str =
  let result = ref asm_str in

  (* Rewrite variants with register: "TLBI VAE1,Xn" -> "TLBI VAE1IS,Xn" *)
  List.iter (fun op ->
    (* Match "TLBI op," but not "TLBI opIS," (case insensitive) *)
    let pattern = Str.regexp_case_fold
      (Printf.sprintf "\\(TLBI[ \t]+\\)\\(%s\\)\\([ \t]*,\\)" op) in
    result := Str.global_replace pattern "\\1\\2IS\\3" !result
  ) tlbi_with_reg;

  (* Rewrite variants without register: "TLBI VMALLE1" -> "TLBI VMALLE1IS" *)
  List.iter (fun op ->
    let pattern = Str.regexp_case_fold
      (Printf.sprintf "\\(TLBI[ \t]+\\)\\(%s\\)\\([ \t]*\\($\\|[\n\r]\\)\\)" op) in
    result := Str.global_replace pattern "\\1\\2IS\\3" !result
  ) tlbi_no_reg;

  !result

(** {1 Register Name Normalization}

    ArchSem uses R0-R30 format for general-purpose registers,
    while ARM assembly uses X0-X30. We normalize to R format. *)

(** [normalize_register reg] converts X-prefixed register names to R-prefixed.
    Returns the original name if not an X register.

    Examples:
    - "X0" -> "R0"
    - "X30" -> "R30"
    - "SP" -> "SP" (unchanged) *)
let normalize_register reg =
  if String.length reg >= 2 &&
     (reg.[0] = 'X' || reg.[0] = 'x') &&
     let rest = String.sub reg 1 (String.length reg - 1) in
     try ignore (int_of_string rest); true with _ -> false
  then
    "R" ^ String.sub reg 1 (String.length reg - 1)
  else
    reg

(** {1 Combined Rewriting}

    Apply all instruction-level rewrites before assembly encoding. *)

(** [rewrite_assembly asm_str] applies all instruction rewrites to assembly code.
    Currently applies:
    - TLBI IS conversion *)
let rewrite_assembly asm_str =
  rewrite_tlbi_to_is asm_str
