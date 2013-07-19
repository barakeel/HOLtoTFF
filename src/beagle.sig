signature beagle =
sig
  
  include Abbrev

 
  (* beagle_prepare *)
  val beagle_firststep : thm list -> goal -> term
  val beagle_monomorph : term -> bool -> term
  val beagle_conv : conv
  val beagle_laststep : thm -> (thm * goal)
  val beagle_prepare : thm list -> goal -> bool -> (thm * goal)    
  
  val beagle : string -> thm list -> goal -> bool -> bool -> OS.Process.status
  val BEAGLE_TAC : thm list -> tactic

end