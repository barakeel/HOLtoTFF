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
  
val DEFUNCT_TAC : tactic 

val bool_bv_conv : conv
  val bool_bv_conv_sub : conv 


end
