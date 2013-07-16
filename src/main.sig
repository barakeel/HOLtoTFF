signature main =
sig
  
  include Abbrev

  val directory : string
  val main_conv : conv
  val beagle_prepare : thm list -> goal -> (thm * goal)    
  val main : string -> thm list -> goal -> bool -> OS.Process.status
  val BEAGLE_TAC : thm list -> tactic

end