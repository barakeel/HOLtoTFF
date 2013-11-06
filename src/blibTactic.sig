signature blibTactic =
sig

include Abbrev
 
  val PROBLEM_TO_GOAL_TAC : thm list -> tactic
    val CONJ_HYP_TAC : tactic 
    val ASSUME_THML_TAC : thm list -> tactic
   
  val BEAGLE_CONV_TAC : tactic
    val CNF_CONV_TAC : tactic
    val FUN_CONV_TAC : tactic
    val BOOL_CONV_TAC : tactic
    
  val BEAGLE_CLAUSE_SET_TAC : tactic 
    val ERASE_EXISTS_TAC : tactic
    val FORALL_CONJUNCTS_TAC : tactic
    val STRIP_CONJ_ONLY_HYP_TAC : tactic
    val ERASE_FORALL_TAC : tactic
    val ADD_HIGHER_ORDER_TAC : tactic 
    val BOOL_BV_TAC : tactic
    val ADD_BOOL_AXIOM_TAC : tactic

end