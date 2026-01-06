open Convert_isla_lib

let () =
  let usage = "Usage: " ^ Sys.argv.(0) ^ " <toml_file> [-o <output_dir>]" in
  let rec parse_args args input_file output_dir =
    match args with
    | [] -> (input_file, output_dir)
    | "-o" :: dir :: rest -> parse_args rest input_file (Some dir)
    | f :: rest -> if input_file = None then parse_args rest (Some f) output_dir else failwith usage
  in
  let (input_file, output_dir) =
      try parse_args (List.tl (Array.to_list Sys.argv)) None None
      with _ -> (None, None)
  in
  match input_file with
  | Some f ->
      Symbols.reset (); (* Ensure clean state *)
      (match output_dir with
       | Some dir ->
           let basename = Filename.basename f in
           let out_path = Filename.concat dir basename in
           let oc = open_out out_path in
           (try Converter.process_toml f oc with e -> close_out oc; raise e);
           close_out oc
       | None -> Converter.process_toml f stdout)
  | None -> Printf.eprintf "%s\n" usage
