signature blibBtactic =
sig

include Abbrev
  
  val mk_tac1 : (goal -> goal) -> (goal -> thm -> thm) -> tactic
  val conv_hypg : conv -> goal -> goal
  val CONV_HYP_TAC : conv -> tactic 
  val list_ASSUME_TAC : thm list -> tactic
  
end