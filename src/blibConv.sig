signature blibConv =
sig

include Abbrev
 
val fun_conv : conv
  val find_free_abs : term -> term list
  val fun_axiom : term -> thm
  val fun_conv_sub : term -> conv

val bool_conv : conv 
  val find_free_bool : term -> term list
  val bool_conv_sub : term -> conv
  val bool_conv_sub_one : conv
  val bool_conv_sub_all : conv

val app_conv : string -> conv

val num_conv : conv
  val find_free_num : term -> term list
  val find_bound_num : term -> term list
  val num_axiom : term -> thm
  val num_conv_conj : term list -> term -> thm
  val num_conv_imp : term list -> term -> thm
  
val fnum_axiom : (term * int) -> thm

end