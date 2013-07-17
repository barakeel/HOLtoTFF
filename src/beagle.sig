signature beagle =
sig
  
  include Abbrev

  val beagle_conv : conv
  val beagle_prepare : thm list -> goal -> bool -> (thm * goal)    
  val beagle : string -> thm list -> goal -> bool -> bool -> OS.Process.status
  val BEAGLE_TAC : thm list -> tactic

end