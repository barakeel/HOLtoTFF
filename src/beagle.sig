signature beagle =
sig
  
  include Abbrev

  val BEAGLE_PROVE : thm list -> goal -> thm
  val BEAGLE_NF_TAC : thm list -> tactic
  val beagle_interact : string -> goal -> OS.Process.status

end