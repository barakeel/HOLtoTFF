signature beagle =
sig
  
  include Abbrev
  
  val BEAGLE_TAC : thm list -> tactic
    val beagle_tac_aux : string -> thm list -> tactic
    val beagle_tac_poly : string -> thm list -> tactic
    val BEAGLE_NF_TAC : thm list -> tactic
    val beagle_interact : string -> goal -> unit
    
  val PROBLEM_TO_GOAL_TAC : thm list -> tactic
    val CONJ_ALL_HYP_TAC : tactic 
    val ASSUME_THML_TAC : thm list -> tactic
 
  val BEAGLE_CONV_TAC : tactic
    val beagle_conv : conv
    
  val BEAGLE_CLAUSE_SET_TAC : tactic 
    val ERASE_EXISTS_TAC : tactic
    val FORALL_CONJUNCTS_TAC : tactic
    val STRIP_CONJ_GOAL_TAC : tactic
    val ERASE_FORALL_TAC : tactic
    val ADD_BOOL_AXIOM_TAC : tactic
    val ADD_HIGHER_ORDER_TAC : tactic 

end