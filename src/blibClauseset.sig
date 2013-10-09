signature blibClauseset =
sig

include Abbrev

  val forall_conjuncts_conv : conv
  val bool_bv_conv_sub : conv 
  val bool_bv_conv : conv
  
  (*
  val ORIENT_NUM_INEQ_CONV : conv
  val NUM_INT_FUN_CONV : term list -> conv
    val NUM_INT_FUN_CONV_SUB : term list -> conv
  val REMOVE_INT_INJECTION_CONV : conv
  val numfun_test : term -> bool
  val numfun_axiom : term -> thm
  *)
  
end