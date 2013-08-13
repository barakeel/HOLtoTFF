signature clausesettools =
sig

include Abbrev

  val forall_conjuncts_conv : conv
  
  val def_conv : conv
  val remove_unused_def : term -> rule
  val remove_unused_defl : term list -> rule
  val remove_unused_appl : term list -> rule

end