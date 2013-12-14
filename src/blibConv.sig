signature blibConv =
sig

include Abbrev
 
  val FUN_CONV : conv
  val BOOL_CONV : conv 
  val DEFUNCT_TAC : tactic 
  val BOOL_BV_CONV : conv

end