signature blibPredicate =
sig

  include Abbrev

  val find_atoml : term -> term list 
  val has_boolarg : term -> bool
  val has_boolarg_thm : thm -> bool
  val has_boolarg_goal : goal -> bool

end