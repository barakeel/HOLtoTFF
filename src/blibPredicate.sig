signature blibPredicate =
sig

  include Abbrev

  val find_atoml : term -> term list 
  val find_pred : term -> term list 
  val is_pred_in : term -> term -> bool
  val has_boolarg : term -> bool
  val has_boolarg_thm : thm -> bool
  val has_boolarg_goal : goal -> bool

end