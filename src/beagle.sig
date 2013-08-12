signature beagle =
sig
  
  include Abbrev
  
  val BEAGLE_TAC : thm list -> tactic
  val beagle_tac_aux : string -> thm list -> tactic
  val BEAGLE_NF_TAC : thm list -> tactic
  val beagle_interact : string -> goal -> unit
    
end