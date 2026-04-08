type reg_state =
  { tid : int;
    regname : string;
    value : int
  }

type mem_state =
  { sym : string;
    addr : int;
    size : int;
    value : int
  }

module Make (Arch : Archsem.Arch) = struct
  open Arch

  let get_thread_regname_pairs (reg_cond : Testrepr.thread_cond list) :
    (int * string) list
    =
    List.concat_map
      (fun (thread, reg_pair) ->
         List.map (fun (name, _) -> (thread, name)) reg_pair
       )
      reg_cond

  let compare_mem_id
        (mem_cond_1 : Testrepr.mem_cond)
        (mem_cond_2 : Testrepr.mem_cond)
    =
    String.compare mem_cond_1.sym mem_cond_2.sym

  let get_unique_conds_ignoring_value
        (conds : (Testrepr.thread_cond list * Testrepr.mem_cond list) list) :
    (int * string) list * Testrepr.mem_cond list
    =
    (* Assuming that each (Testrepr.thread_cond list * Testrepr.mem_cond list) already contains unique values *)
    List.fold_left
      (fun (acc_reg_cond, acc_mem_cond) (reg_cond, mem_cond) ->
         let new_reg_cond = get_thread_regname_pairs reg_cond in
         ( List.sort_uniq compare (acc_reg_cond @ new_reg_cond),
           List.sort_uniq compare_mem_id (acc_mem_cond @ mem_cond)
         )
       )
      ([], []) conds

  let minimise_reg_state (reg_conds : (int * string) list) (state : ArchState.t) :
    reg_state list
    =
    List.map
      (fun (tid, regname) ->
         let regs = ArchState.reg tid state in
         let value = RegMap.geti (Reg.of_string regname) regs in
         {tid; regname; value}
       )
      reg_conds

  let minimise_mem_state (mem_conds : Testrepr.mem_cond list) (state : ArchState.t)
    : mem_state list
    =
    let mem = ArchState.mem state in
    List.map
      (fun (mc : Testrepr.mem_cond) ->
         match MemMap.lookupi_opt mc.addr mc.size mem with
         | None ->
             failwith
               (Printf.sprintf "[[outcome]] memory not found at 0x%x" mc.addr)
         | Some mv -> {sym = mc.sym; addr = mc.addr; size = mc.size; value = mv}
       )
      mem_conds

  let minimise_states
        ((reg_conds, mem_conds) : (int * string) list * Testrepr.mem_cond list)
        (states : ArchState.t list) : (reg_state list * mem_state list) list
    =
    List.map
      (fun state ->
         (minimise_reg_state reg_conds state, minimise_mem_state mem_conds state)
       )
      states

  let compare_minimised_states
        ((regs1, mems1) : reg_state list * mem_state list)
        ((regs2, mems2) : reg_state list * mem_state list) : int
    =
    let c =
      List.compare
        (fun (r1 : reg_state) (r2 : reg_state) -> Int.compare r1.value r2.value)
        regs1 regs2
    in
    if c <> 0 then c
    else List.compare (fun m1 m2 -> Int.compare m1.value m2.value) mems1 mems2

  let final_regs_to_string (rs : reg_state list) =
    String.concat " "
      (List.map
         (fun (r : reg_state) ->
            Printf.sprintf "%d:%s=%d;" r.tid r.regname r.value
          )
         rs
      )

  let final_mem_to_string (ms : mem_state list) =
    String.concat " "
      (List.map
         (fun (m : mem_state) -> Printf.sprintf "[%s]=%d;" m.sym m.value)
         ms
      )
end
