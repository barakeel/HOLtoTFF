signature blibBconv =
sig

  include Abbrev

  val REPEAT_N_CONV : int -> conv -> conv 
  val not_strip_exists_conv : conv
  val strip_forall_not_conv : conv
  val ARG_CONV : conv -> conv
  val forall_conjuncts_conv : conv
  
end  