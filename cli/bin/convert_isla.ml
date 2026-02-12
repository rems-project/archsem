open Isla_converter
open Cmdliner

type mode = VM | UM

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

(** {1 Entry Point} *)

let run input_file output_dir mode =
  let usermode = (mode = UM) in
  match output_dir with
  | Some dir -> convert_to_file ~usermode input_file dir
  | None -> convert ~usermode input_file stdout

let cmd =
  let doc = "Convert isla format litmus tests to archsem format" in
  let info = Cmd.info "convert_isla" ~doc in
  Cmd.v info Term.(const run $ input_file_t $ output_dir_t $ mode_t)

let () = exit (Cmd.eval cmd)
