open Isla_converter

type mode = VM | UM

let () =
  let usage = "Usage: " ^ Sys.argv.(0) ^ " <toml_file> [-o <output_dir>] [--mode <vm|um>]" in
  let rec parse_args args input_file output_dir mode =
    match args with
    | [] -> (input_file, output_dir, mode)
    | "-o" :: dir :: rest -> parse_args rest input_file (Some dir) mode
    | "--mode" :: "vm" :: rest -> parse_args rest input_file output_dir VM
    | "--mode" :: "um" :: rest -> parse_args rest input_file output_dir UM
    | "--mode" :: _ :: _ -> failwith "Invalid mode. Use 'vm' or 'um'"
    | f :: rest -> if input_file = None then parse_args rest (Some f) output_dir mode else failwith usage
  in
  let (input_file, output_dir, mode) =
      try parse_args (List.tl (Array.to_list Sys.argv)) None None VM
      with Failure msg -> Printf.eprintf "%s\n" msg; exit 1
  in
  let usermode = (mode = UM) in
  match input_file with
  | Some f ->
      Symbols.reset (); (* Ensure clean state *)
      (match output_dir with
       | Some dir ->
           let basename = Filename.basename f in
           let out_path = Filename.concat dir basename in
           let oc = open_out out_path in
           (try Converter.process_toml ~usermode f oc with e -> close_out oc; raise e);
           close_out oc
       | None -> Converter.process_toml ~usermode f stdout)
  | None -> Printf.eprintf "%s\n" usage; exit 1
