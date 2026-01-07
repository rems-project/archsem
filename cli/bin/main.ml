open Archsem

let () =
  if Array.length Sys.argv < 3 then
    Printf.eprintf "Usage: %s <model: seq|ump|vmp> <test_file.toml>\n" Sys.argv.(0)
  else
    let model_str = Sys.argv.(1) in
    let filename = Sys.argv.(2) in

    (* Wrap vmp model with default parameters: debug=false, mem_strict=false, bbm_check=true *)
    let vmp_model fuel term state =
      vmProm_model fuel false false true term state
    in

    let model =
      match model_str with
      | "seq" -> seq_model
      | "ump" -> umProm_model
      | "vmp" -> vmp_model
      | _ -> failwith ("Unknown model: " ^ model_str ^ ". Supported: seq, ump, vmp")
    in

    let success = Archsem_test.Litmus_runner.run_litmus_test model filename in
    if success then exit 0 else exit 1
