signature tools =
sig

  include Abbrev

(* aconv *)
  val is_member_aconv : term -> term list -> bool
  val erase_double_aconv : term list -> term list 
  val is_member_aconv_arity : (term * int) -> (term * int) list -> bool 
  val erase_double_aconv_arity : (term * int) list -> (term * int) list
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
(* arity *)
  val get_arity : term -> int
  val collapse_lowestarity : (term * int) list -> (term * int) list   
(* conv *)
  val repeat_n_conv : int -> conv -> conv 
  val not_exists_list_conv : conv
(* rule *)
  val conv_concl : conv -> thm -> thm 
  val conv_concl_hyp : conv -> term -> thm -> thm
  val list_prove_hyp : thm list -> thm -> thm 
  val list_conj_hyp : thm -> thm
  val list_ap_thm : thm -> term list -> thm 
  val list_fun_eq_conv : term list -> term -> thm
  val repeat_rule : int -> rule -> rule
(* extraction *)
  val all_subterm : term -> term list
  val all_type : term -> hol_type list
  val all_vartype : term -> hol_type list
(* first order *)  
  val find_atoml : term -> term list 
  val find_predicatel : term -> term list 
  val is_predicate_in : term -> term -> bool
  val find_unpredicatel : term -> term list
  val has_boolarg : term -> bool
  val has_boolarg_thm : thm -> bool

end