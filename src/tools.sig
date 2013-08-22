signature tools =
sig

  include Abbrev

(* basic *)
  val repeat_n_fun :  int -> ('a -> 'a) -> 'a -> 'a
(* error handling *)
  val success : ('a -> 'b) -> 'a -> bool
  val wrap : string -> string -> string -> ('a -> 'b) -> 'a -> 'b
(* aconv *)
  val is_member_term : term -> term list -> bool
  val erase_double_term : term list -> term list 
(* test *) 
  val has_boolty : term -> bool  
  val has_numty : term -> bool
  val is_not_var : term -> bool 
  val is_var_or_const : term -> bool 
(* quantifier *) 
  val strip_quant : term -> (term list * term)
  val bound_by_quant : term -> term -> bool 
(* name *)  
  val name_of : term -> string
  val name_tff : string -> term -> string
  val name_numeral : term -> string
  val is_dc : term -> bool
  val is_not_dc : term -> bool
  val is_dca : (term * int) -> bool
  val is_not_dca : (term * int) -> bool
  val is_not_dcaty : ((term * int) * string) -> bool
(* term *)
  val strip_comb_n : (term * int) -> (term * term list)
  val get_arity : term -> int
(* thm *)
  val only_hyp : thm -> term
  val is_refl : thm -> bool
(* goal *)
  val only_hypg : goal -> term
  val mk_goal : thm -> goal 
  val is_subset_goal : goal -> goal -> bool
  val thm_test : thm -> goal -> string -> thm
  val goal_to_string : goal -> string
(* conv *)
  val repeat_n_conv : int -> conv -> conv 
  val not_strip_exists_conv : conv
  val strip_forall_not_conv : conv
(* rule *)
  val conv_concl : conv -> thm -> thm 
  val conv_onehyp : conv -> term -> thm -> thm
  val conv_hypl : conv -> term list -> thm -> thm
  val list_PROVE_HYP : thm list -> thm -> thm 
  val list_conj_hyp_rule : thm -> thm
  val unconj_hyp_rule : term -> thm -> thm
  val list_unconj_hyp_rule : term list -> thm -> thm 
  val strip_conj_hyp_rule : thm -> thm 
  val list_AP_THM : thm -> term list -> thm 
  val list_FUN_EQ_CONV : term list -> term -> thm
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
  val find_pred : term -> term list 
  val is_pred_in : term -> term -> bool
  val find_unpred : term -> term list
  val has_boolarg : term -> bool
  val has_boolarg_thm : thm -> bool
  val has_boolarg_goal : goal -> bool


end