signature blibSyntax =
sig

  include Abbrev
  (* aconv *)
  val is_member_aconv : term -> term list -> bool
  val erase_aconv : term list -> term list 
  val merge_aconv : term list list -> term list 
  (* test *) 
  val has_boolty : term -> bool  
  val has_numty : term -> bool
  val has_intty : term -> bool
  val is_var_or_const : term -> bool 
  (* quantifier *) 
  val strip_quant : term -> (term list * term)
  (* var *)
  val namev_of : term -> string
  (* term *)
  val strip_comb_n : int -> term -> (term * term list)
  val get_arity : term -> int
  val less_term : (term * term) -> bool
  (* thm *)
  val only_hyp : thm -> term
  val is_refl : thm -> bool
  (* goal *)
  val only_hypg : goal -> term
  val mk_goal : thm -> goal 
  val is_subset_goal : goal -> goal -> bool
  val goal_to_string : goal -> string
  (* boolean argument *)
  val find_atoml : term -> term list 
  val has_boolarg : term -> bool
  val has_boolarg_thm : thm -> bool
  val has_boolarg_goal : goal -> bool
  
end