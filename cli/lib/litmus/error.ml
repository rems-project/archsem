(** Structured error handling for the CLI.

    All CLI-originated errors raise {!Cli_error} with an {!origin} tag,
    enabling the runner to distinguish parse-time errors from model crashes.

    {2 Error output format}

    The runner displays errors as:
    {v  ✗ test.toml  [origin] ctx: message v}

    where [origin] comes from {!origin}, and [ctx] is an optional location
    hint provided via {!raise_error_ctx}.

*)

(** Error origin — which logical subsystem raised the error. *)
type origin =
  | Config  (** Configuration file or CLI flag validation *)
  | Parser  (** TOML/term/assertion parsing *)
  | Converter  (** Isla IR to Testrepr conversion *)
  | Assembler  (** External assembler invocation *)
  | Symbols  (** Symbol table resolution *)
  | Printer  (** TOML output and file writing *)
  | Runner  (** Test execution and outcome checking *)

(** The single exception type for all CLI errors.

    Caught by {!Runner.run_litmus_test} which uses nested [try-with]:
    - Outer: parse phase errors ({!Cli_error} or [Otoml] exceptions) → [SetupError]
    - Inner: run phase — {!Cli_error} from outcome checking → [ModelError];
      unrecognised exceptions (Coq model crash) → [ModelError] *)
exception Cli_error of origin * string

(** Human-readable origin label for error output. *)
let string_of_origin = function
  | Config -> "config"
  | Parser -> "parser"
  | Converter -> "converter"
  | Assembler -> "assembler"
  | Symbols -> "symbols"
  | Printer -> "printer"
  | Runner -> "runner"

(** Raise a {!Cli_error} with a formatted message.

    {[
      Error.raise_error Config "must be positive"
      (* raises Cli_error (Config, "must be positive") *)

      Error.raise_error Parser "unknown architecture: %s" arch
      (* raises Cli_error (Parser, "unknown architecture: MIPS") *)
    ]} *)
let raise_error origin fmt =
  Printf.ksprintf (fun msg -> raise (Cli_error (origin, msg))) fmt

(** Raise a {!Cli_error} with a context hint prepended to the message.

    Use [~ctx] to indicate {e where} in the input the error occurred —
    a TOML key path, symbol name, register, or any relevant locator.

    {[
      Error.raise_error_ctx Config ~ctx:"assembler.instruction_step"
        "must be positive"
      (* raises Cli_error (Config, "assembler.instruction_step: must be positive") *)

      Error.raise_error_ctx Symbols ~ctx:"x" "unknown symbol"
      (* raises Cli_error (Symbols, "x: unknown symbol") *)

      Error.raise_error_ctx Runner ~ctx:"outcome.0:X0"
        "register not found in final state"
      (* raises Cli_error (Runner, "outcome.0:X0: register not found ...") *)
    ]} *)
let raise_error_ctx origin ~ctx fmt =
  Printf.ksprintf (fun msg -> raise (Cli_error (origin, ctx ^ ": " ^ msg))) fmt
