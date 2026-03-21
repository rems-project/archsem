module RegValGen = RegValGen

module Utils = Utils

module type Arch = Arch.Arch

type empty = Utils.empty

module Arm : sig
  include Arch.Arch

  val tiny_isa : iSem

  val umProm_model : empty ArchModel.t

  module BBM : sig
    type param =
      | Off
      | Lax
      | Strict
  end

  val vmProm_model : ?bbm_param:BBM.param -> empty ArchModel.t

end

module X86 : sig
  include Arch.Arch

  val tiny_isa : iSem

  val tso_model : ?allow_eager:bool -> empty ArchModel.t
end
