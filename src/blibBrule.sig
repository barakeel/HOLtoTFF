signature blibBrule =
sig

  include Abbrev
 
  val STRIP_SYM : rule
  val LIST_PROVE_HYP : thm list -> rule
  val LIST_AP_THM : thm -> term list -> thm 
  val EXTL : term list -> rule
  val REMOVE_DEFL : term list -> rule
  
end