signature blibSyntax =
sig

  include Abbrev
  (* aconv *)
  val is_member_aconv : term -> term list -> bool
  val erase_double_aconv : term list -> term list 
  (* test *) 
  val has_boolty : term -> bool  
  val has_numty : term -> bool
  val has_intty : term -> bool
  val is_var_or_const : term -> bool 
  val is_leaf : term -> bool
  (* quantifier *) 
  val strip_quant : term -> (term list * term)
  val bound_by_quant : term -> term -> bool 
  (* var *)
  val name_of : term -> string
  (* term *)
  val strip_comb_n : (term * int) -> (term * term list)
  val get_arity : term -> int
  val all_fosubterm : term -> term list
  (* thm *)
  val only_hyp : thm -> term
  val is_refl : thm -> bool
  (* goal *)
  val only_hypg : goal -> term
  val mk_goal : thm -> goal 
  val is_subset_goal : goal -> goal -> bool
  val thm_test : thm -> goal -> string -> thm
  val goal_to_string : goal -> string
  
end