signature rule =
sig

  type thm = Thm.thm

  val negate_concl : thm -> thm 
  val negate_concl_rev : term -> thm -> thm

  val add_bool_axioms : thm -> thm 
  val remove_bool_axioms : thm -> thm
  
  val remove_exists : term -> thm -> thm 
  val remove_exists_thm : thm -> thm
  val add_exists : (term * term list) -> thm -> thm 
  val add_existsl : (term * term list) list -> thm -> thm 

end