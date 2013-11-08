signature blibHO =
sig

  include Abbrev
   
  val collapse_lowestarity : (term * int) list -> (term * int) list         
  val firstorder      : term -> bool
  val firstorder_err  : term -> bool 
  val firstorder_goal : goal -> bool
  val firstorder_thm  : thm  -> bool 
 
end