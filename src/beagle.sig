signature beagle =
sig
  
  include Abbrev
  val BEAGLE_TAC : thm list -> tactic
  val beagle_nf : (thm list * goal) -> goal
    
end