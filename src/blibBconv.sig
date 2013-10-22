signature blibBconv =
sig

  include Abbrev

  val repeat_n_conv : int -> conv -> conv 
  val not_strip_exists_conv : conv
  val strip_forall_not_conv : conv
  val forall_conjuncts_conv : conv
  
end  