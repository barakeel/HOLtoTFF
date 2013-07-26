signature beagle =
sig
  
  include Abbrev
  (* beagle_prepare *)
  val beagle_firststep : ppstream -> thm list -> goal -> thm
  val beagle_conv : ppstream -> conv
  val beagle_laststep : ppstream -> thm -> goal
  val beagle_prepare : ppstream -> thm list -> goal -> bool -> goal    
   
  val beagle : string -> thm list -> goal -> bool -> unit
  val BEAGLE_TAC : thm list -> tactic
  
end