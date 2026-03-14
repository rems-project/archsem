module RegValGen = RegValGen

module Utils = Utils

module type Arch = Arch.Arch

type empty = Utils.empty

module Arm = struct
  module Required = struct
    module Arch = ArmInst.Arch

    include ArmInst.Arm

    let default_address_space = System_types.PAS_NonSecure
  end

  include ArchBuild.Build(Required)

  let tiny_isa = (ArmInst.sail_tiny_arm_sem true)

  let termCond_to_coq (term : termCond) tid rm =
    let tc = List.nth term (Z.to_int tid) in
    tc rm

  let umProm_model isem fuel term initState =
    UMPromising.coq_UMPromising_pf isem (Z.of_int fuel)
      (ArchState.num_thread initState |> Z.of_int) (termCond_to_coq term) initState
    |> Obj.magic

  module BBM = VMPromising.BBM

  let vmProm_model ?(bbm_param = BBM.Off) isem fuel term initState =
    VMPromising.coq_VMPromising_pf bbm_param isem (Z.of_int fuel)
      (ArchState.num_thread initState |> Z.of_int) (termCond_to_coq term) initState
    |> Obj.magic
end

module X86 = struct
  module Required = struct
    module Arch = X86Inst.Arch

    include X86Inst.X86

    let default_address_space = ()
  end

  include ArchBuild.Build(Required)

  let tiny_isa = (X86Inst.sail_tiny_x86_sem true)

  let termCond_to_coq (term : termCond) tid rm =
    let tc = List.nth term (Z.to_int tid) in
    tc rm

  let tso_model isem fuel term initState =
    OperationalX86TSO.x86_operational_modelc (Z.of_int fuel) isem
      (ArchState.num_thread initState |> Z.of_int) (termCond_to_coq term)
      initState
    |> Obj.magic

end
