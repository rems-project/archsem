open Archsem

let init_reg =
  let open RegMap in
  empty
  |> inserti Reg.pc 0x500
  |> inserti (Reg.r 0) 0x0
  |> inserti (Reg.r 1) 0x11111
  |> inserti (Reg.r 2) 0x10101
  |> inserti (Reg.sctlr 1) 0x0
  |> insert
    (RegVal.of_gen Reg.pstate (Struct [("EL", Number (Z.zero))]) |> Result.get_ok)

let number_xor = 10

let init_mem =
  let cell = ref MemMap.empty in
  for i = 0 to number_xor do
    cell := MemMap.inserti (0x500 + 4 * i) 4 0xca020020 !cell
  done;
  !cell

let termCond = [(fun pc0 -> Z.equal pc0 (Z.of_int (0x500 + 4 * number_xor)))]

let initState = ArchState.make [init_reg] init_mem

let test =
  let t = Sys.time() in
  for _ = 0 to 999 do
    let _ = seq_model 100 termCond initState in ()
  done;
  let x = seq_model 100 termCond initState in
  Printf.printf "Seq execution time (%i): %fs\n" (1000 * number_xor) (Sys.time() -. t);
  x

let _test_prom =
  let t = Sys.time() in
  for _ = 0 to 99 do
    let _ = umProm_model 100 termCond initState in ()
  done;
  let x = umProm_model 10000000 termCond initState in
  Printf.printf "Prom execution time (%i): %fs\n" (100 * number_xor) (Sys.time() -. t);
  x


let r0_extract (res : empty ArchModel.Res.t) : int =
  match res with
  | Error s -> raise (Failure s)
  | Flagged _ -> .
  | FinalState fs -> RegMap.geti (Reg.r 0) (ArchState.reg 0 fs)


let value = r0_extract (List.hd test)

let _ = Printf.printf "Number of results %i\n" (List.length test)

let _ = Printf.printf "Final R0 0x%x\n" value
