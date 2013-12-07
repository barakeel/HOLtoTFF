signature blibBrule =
sig

  include Abbrev
 
  val STRIP_SYM : rule
  val CONV_RULE : conv -> thm -> thm 
  val CONV_HYPO_RULE : conv -> term -> thm -> thm
  val CONV_HYPL_RULE : conv -> term list -> thm -> thm
  val list_PROVE_HYP : thm list -> thm -> thm 
  
  val list_DISJ_CASES_UNION : term -> thm list -> thm
  val list_conj_hyp_rule : thm -> thm
  val unconj_hyp_rule : term -> thm -> thm
  val list_unconj_hyp_rule : term list -> thm -> thm 
  val strip_conj_hyp_rule : thm -> thm 
  
  val list_AP_THM : thm -> term list -> thm 
  val list_FUN_EQ_CONV : term list -> term -> thm
  val repeat_rule : int -> rule -> rule
  val EXTL : term list -> rule
  val list_TRANS : thm list -> thm
  
  val remove_def : term -> rule
  val remove_defl : term list -> rule
  
end