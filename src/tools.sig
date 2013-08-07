signature tools =
sig

  include Abbrev

(* aconv *)
  val is_member_term : term -> term list -> bool
  val erase_double_term : term list -> term list 

(* test *) 
  val has_boolty : term -> bool  
  val has_numty : term -> bool
  val is_var_or_const : term -> bool 
  val is_logical : term -> bool
  val is_new_axiom : term list -> thm -> bool 
  val is_not_var : term -> bool 
(* quantifier *) 
  val strip_quant : term -> (term list * term)
  val bound_by_quant : term -> term -> bool 
(* name *)  
  val name_of : term -> string
  val name_tff : string -> term -> string
  val name_numeral : term -> string
(* term *)
  val strip_comb_n : (term * int) -> (term * term list)
  val list_mk_var : (string list * hol_type list) -> term list
(* thm *)
val only_hyp : thm -> term
val thm_eq : thm -> thm -> bool
(* goal *)
val only_hypg : goal -> term
val mk_goal : thm -> goal 
val goal_eq : goal -> goal -> bool
(* arity *)
  val get_arity : term -> int
  val collapse_lowestarity : (term * int) list -> (term * int) list   
(* conv *)
  val repeat_n_conv : int -> conv -> conv 
  val not_strip_exists_conv : conv
  val strip_forall_not_conv : conv
(* rule *)
  val conv_concl : conv -> thm -> thm 
  val conv_hyp : conv -> term -> thm -> thm
  val conv_hypl : conv -> term list -> thm -> thm
  val list_PROVE_HYP : thm list -> thm -> thm 
  val list_conj_hyp : thm -> thm
  val unconj_hyp : term -> thm -> thm
  val list_unconj_hyp : term list -> thm -> thm 
  val strip_conj_hyp : thm -> thm 
  val list_ap_thm : thm -> term list -> thm 
  val list_fun_eq_conv : term list -> term -> thm
  val repeat_rule : int -> rule -> rule
  val EXTL : term list -> rule
  val list_TRANS : thm list -> thm
(* extraction *)
  val all_subterm : term -> term list
  val all_type : term -> hol_type list
  val all_subtype : term -> hol_type list
  val all_leaftype : term -> hol_type list
  val all_vartype : term -> hol_type list
(* first order *)  
  val find_atoml : term -> term list 
  val find_predicatel : term -> term list 
  val is_predicate_in : term -> term -> bool
  val find_unpredicatel : term -> term list
  val has_boolarg : term -> bool
  val has_boolarg_thm : thm -> bool
  val has_boolarg_goal : goal -> bool
(* polymorph *)
  val is_polymorph : term -> bool 
  val is_polymorph_goal : goal -> bool 
  val is_polymorph_thm : thm -> bool
  val is_polymorph_pb : thm list -> goal -> bool 

end