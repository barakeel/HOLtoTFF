signature blibBtactic =
sig

include Abbrev
  
  val mk_tac1 : (goal -> goal) -> (goal -> thm -> thm) -> tactic
  val conv_hyp : conv -> goal -> goal
  val CONV_HYP_TAC : conv -> tactic 
  val LIST_ASSUME_TAC : thm list -> tactic
  val REMOVE_HYPL_TAC : term list -> tactic

end