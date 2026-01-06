open Archsem

let () =
  if Array.length Sys.argv < 3 then
    Printf.eprintf "Usage: %s <model: seq|ump> <test_file.toml>\n" Sys.argv.(0)
  else
    let model_str = Sys.argv.(1) in
    let filename = Sys.argv.(2) in

    let model =
      match model_str with
      | "seq" -> seq_model
      | "ump" -> umProm_model
      | _ -> failwith ("Unknown model: " ^ model_str ^ ". Supported: seq, ump")
    in

    let success = Archsem_test.Litmus_runner.process_file model filename in
    if success then exit 0 else exit 1
