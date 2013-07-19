signature conv =
sig

  include Abbrev
 
  (* conv *)
  val beta_conv : conv
  val eta_conv : conv
 
  val find_free_bool : term -> term list
  val find_bound_bool : term -> term list
  val bool_conv_sub : term -> term -> thm
  val bool_conv : conv
  
  val fun_conv : conv
 
  val app_conv : string -> conv

  val find_free_num : term -> term list
  val find_bound_num : term -> term list
  val num_axiom : term -> thm
  val num_conv_conj : term list -> term -> thm
  val num_conv_imp : term list -> term -> thm
  val num_conv : conv
 
  
  val define_conv : conv
  
 
 
end
