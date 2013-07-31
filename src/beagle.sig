signature beagle =
sig
  
  include Abbrev
  (* beagle_nf *)
  val problem_to_hypterm : thm list -> goal -> term
  val beagle_conv : ppstream -> conv
  val beagle_clauseset : term -> term list
  val beagle_nf : ppstream -> thm list -> goal -> bool -> term list 
   
  val beagle : string -> thm list -> goal -> bool -> unit
  val BEAGLE_TAC : thm list -> tactic
  
end