open Archsem

let () =
  if Array.length Sys.argv < 3 then
    Printf.eprintf "Usage: %s <model: seq|ump|vmp|ump_pf|vmp_pf|vmp_pf_debug|vmp_pf_bbm> <test_file.toml>\n" Sys.argv.(0)
  else
    let model_str = Sys.argv.(1) in
    let filename = Sys.argv.(2) in

    (* Wrap vmp model with default parameters: debug=false, mem_strict=false, bbm_check=false *)
    let vmp_model fuel term state =
      vmProm_model fuel false false false term state
    in
    let vmp_model_pf fuel term state =
      Archsem.vmp_model_pf fuel false false false term state
    in
    let vmp_model_pf_debug fuel term state =
      Archsem.vmp_model_pf fuel true false false term state
    in
    (* BBM check enabled *)
    let vmp_model_pf_bbm fuel term state =
      Archsem.vmp_model_pf fuel false false true term state
    in

    let model =
      match model_str with
      | "seq" -> seq_model
      | "ump" -> umProm_model
      | "vmp" -> vmp_model
      | "ump_pf" -> umProm_model_pf
      | "vmp_pf" -> vmp_model_pf
      | "vmp_pf_debug" -> vmp_model_pf_debug
      | "vmp_pf_bbm" -> vmp_model_pf_bbm
      | _ -> failwith ("Unknown model: " ^ model_str ^ ". Supported: seq, ump, vmp, ump_pf, vmp_pf, vmp_pf_debug, vmp_pf_bbm")
    in

    let success = Archsem_test.Litmus_runner.run_litmus_test model_str model filename in
    if success then exit 0 else exit 1
