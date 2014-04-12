signature beagle =
sig
  
  include Abbrev
  
  val BEAGLE_ORACLE : int -> int -> thm list -> goal -> bool
  val BEAGLE_PROVE : int -> int -> thm list -> goal -> thm
  val BEAGLE_TAC : int -> int -> thm list -> tactic
  val beagle_nf : (thm list * goal) -> goal
  val beagle_tff : goal -> bool
  val beagle_fof : goal -> bool
  val beagle_filter : int -> int -> thm list * goal -> thm list * goal
  val related_thms : int -> (thm list * goal) -> string list -> thm list
    
end