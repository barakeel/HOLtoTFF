signature main =
sig
  
  include Abbrev

  val directory : string
  val main_conv : conv
  val beagle_prepare : thm list -> goal -> bool -> (thm * goal)    
  val main : string -> thm list -> goal -> bool -> bool -> OS.Process.status
  val BEAGLE_TAC : thm list -> tactic

end