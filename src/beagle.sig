signature beagle =
sig
  
  include Abbrev

  val BEAGLE_PROVE : thm list -> goal -> thm
  val BEAGLE_NF_TAC : thm list -> tactic
  val beagle_interact : string -> goal -> OS.Process.status
  val beagle_filter : string -> goal -> goal
  val related_thms : (thm list * goal) -> string list -> thm list
  
  
end