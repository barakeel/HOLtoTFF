signature blibBrule =
sig

  include Abbrev
 
  val conv_concl : conv -> thm -> thm 
  val conv_onehyp : conv -> term -> thm -> thm
  val conv_hypl : conv -> term list -> thm -> thm
  val list_PROVE_HYP : thm list -> thm -> thm 
  val list_conj_hyp_rule : thm -> thm
  val unconj_hyp_rule : term -> thm -> thm
  val list_unconj_hyp_rule : term list -> thm -> thm 
  val strip_conj_hyp_rule : thm -> thm 
  val list_AP_THM : thm -> term list -> thm 
  val list_FUN_EQ_CONV : term list -> term -> thm
  val repeat_rule : int -> rule -> rule
  val EXTL : term list -> rule
  val list_TRANS : thm list -> thm
  
  val extdef_conv : conv
  val remove_unused_def : term -> rule
  val remove_unused_defl : term list -> rule
  val remove_unused_extdefl : term list -> rule
  
  
end