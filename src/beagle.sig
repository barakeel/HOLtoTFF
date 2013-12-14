signature beagle =
sig
  
  include Abbrev

  val BEAGLE_ORACLE : thm list -> goal -> thm
  val beagle_proof : thm list -> goal -> 
                     (int list * boolSyntax.term) 
                     list
  val BEAGLE_NF_TAC : thm list -> tactic
  val beagle_interact : string -> goal -> OS.Process.status

  
end