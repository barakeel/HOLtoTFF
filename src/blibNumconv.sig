signature blibNumconv =
sig

include Abbrev

(* numeral to integer translation *)
  val ORIENT_NUM_INEQ_CONV : conv
  val INTF_CONV : term list -> conv
    val INTF_CONV_SUB : term list -> conv
  val REMOVE_INT_INJECTION_CONV : conv
  val intf_test : term -> bool
  val intf_axiom : term -> thm
 
(* numeral to numeral translation *)
val num_conv : conv
  val find_free_num : term -> term list
  val find_bound_num : term -> term list
  val num_axiom : term -> thm
  val num_conv_conj : term list -> term -> thm
  val num_conv_imp : term list -> term -> thm
val numf_axiom : (term * int) -> thm
  

end