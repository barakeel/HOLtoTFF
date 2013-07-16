signature conv =
sig

  type term     = Term.term
  type hol_type = Type.hol_type
  type thm = Thm.thm
  type conv = Term.term -> Thm.thm
 
  (* conv *)
  val beta_conv : conv
  val eta_conv : conv
 
  val bool_conv : conv
  val fun_conv : conv
 
  val find_bound_app : term -> (term * int) list
  val find_free_app : term -> (term * int) list
  val app_conv : conv
  
  val num_conv : conv
  
  val predicatedef : term
  val predicate_conv : conv
  
  val define_conv : conv
  
 
 
end
