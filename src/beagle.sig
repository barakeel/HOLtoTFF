signature beagle =
sig
  
  include Abbrev
  
  val BEAGLE_TAC : thm list -> tactic
  val BEAGLE_ORACLE : thm list -> goal -> unit
  val BEAGLE_PROVE : thm list -> goal -> thm
  val BEAGLE_NF_TAC : thm list -> tactic
  val beagle_interact : string -> goal -> unit
  val mk_bcooperthml : thm list -> goal -> thm list
  val get_atomlthml : thm list -> goal -> (term list * thm list)
  
end