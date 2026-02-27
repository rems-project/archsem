open Isla_converter
open Cmdliner

type mode = VM | UM

let parse_assembler s =
  match String.lowercase_ascii s with
  | "llvm" -> Assembler.LLVM "llvm"
  | "gnu" -> Assembler.GNU "aarch64-linux-gnu"
  | prefix when String.contains prefix '-' ->
      (* Treat as a GNU-style prefix, e.g. "aarch64-none-elf" *)
      Assembler.GNU prefix
  | prefix ->
      (* Treat as LLVM prefix, e.g. "llvm-18" *)
      Assembler.LLVM prefix

let convert ~usermode input_file output_channel =
  Symbols.reset ();
  Allocator.reset ();
  Converter.process_toml ~usermode input_file output_channel

let convert_to_file ~usermode input_file output_dir =
  let basename = Filename.basename input_file in
  let out_path = Filename.concat output_dir basename in
  let oc = open_out out_path in
  Fun.protect ~finally:(fun () -> close_out oc) (fun () ->
    convert ~usermode input_file oc
  )

(** {1 Argument Parsing} *)

let input_file_t =
  let doc = "Isla format TOML test file to convert." in
  Arg.(required & pos 0 (some file) None & info [] ~docv:"TOML_FILE" ~doc)

let output_dir_t =
  let doc = "Output directory. If omitted, writes to stdout." in
  Arg.(value & opt (some dir) None & info ["o"] ~docv:"DIR" ~doc)

let mode_t =
  let doc = "Conversion mode. $(b,vm) for virtual memory (default), $(b,um) for usermode." in
  Arg.(value & opt (enum ["vm", VM; "um", UM]) VM & info ["mode"] ~doc)

let assembler_t =
  let doc = "Assembler backend. $(b,llvm) for llvm-mc (default), $(b,gnu) for \
             aarch64-linux-gnu-as, or a custom prefix (e.g. $(b,llvm-18), \
             $(b,aarch64-none-elf))." in
  Arg.(value & opt (some string) None & info ["assembler"] ~docv:"BACKEND" ~doc)

(** {1 Entry Point} *)

let run input_file output_dir mode assembler =
  Option.iter (fun s -> Assembler.set_backend (parse_assembler s)) assembler;
  let usermode = (mode = UM) in
  match output_dir with
  | Some dir -> convert_to_file ~usermode input_file dir
  | None -> convert ~usermode input_file stdout

let cmd =
  let doc = "Convert isla format litmus tests to archsem format" in
  let info = Cmd.info "convert_isla" ~doc in
  Cmd.v info Term.(const run $ input_file_t $ output_dir_t $ mode_t $ assembler_t)

let () = exit (Cmd.eval cmd)
