signature beagle =
sig
  
  include Abbrev

  val BEAGLE_PROVE : bool -> bool -> thm list -> goal -> thm
  val beagle_nf : (thm list * goal) -> goal
  val beagle_interact : string -> goal -> OS.Process.status
  val beagle_unsat : string -> thm list -> goal -> bool
  val beagle_filter : string -> thm list * goal -> thm list * goal
  val related_thms : (thm list * goal) -> string list -> thm list
    
end