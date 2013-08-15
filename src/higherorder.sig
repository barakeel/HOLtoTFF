signature higherorder =
sig

  include Abbrev
           
  val firstorder      : term -> bool
  val firstorder_err  : term -> bool 
  val firstorder_goal : goal -> bool
  val firstorder_thm  : thm  -> bool 
 
end