signature blibBconv =
sig

  include Abbrev
  
  val STRIP_FORALL_NOT_CONV : conv
  val ARG_CONV : conv -> conv
  val LIST_FUN_EQ_CONV : term list -> conv
  val FORALL_CONJUNCTS_CONV : conv
  val INT_NORM_CLAUSE_CONV : conv
  
end  