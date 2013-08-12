signature tactic =
sig

include Abbrev
  
  val mk_tac1 : (goal -> goal) -> (goal -> thm -> thm) -> tactic
  val CONV_ONLY_HYP_TAC : conv -> tactic 

  val PROBLEM_TO_GOAL_TAC : thm list -> tactic
    val CONJ_ALL_HYP_TAC : tactic 
    val ASSUME_THML_TAC : thm list -> tactic
 
  val BEAGLE_CONV_TAC : tactic
    val beagle_conv : conv
    
  val BEAGLE_CLAUSE_SET_TAC : tactic 
    val ERASE_EXISTS_TAC : tactic
    val FORALL_CONJUNCTS_TAC : tactic
    val STRIP_CONJ_ONLY_HYP_TAC : tactic
    val ERASE_FORALL_TAC : tactic
    val ADD_BOOL_AXIOM_TAC : tactic
    val ADD_HIGHER_ORDER_TAC : tactic 

end