signature tools =
sig

type term = Term.term
type hol_type = Type.hol_type
type thm = Thm.thm
type conv = Term.term -> Thm.thm


(* test functions *) 
  val has_boolty : term -> bool  
  val has_numty : term -> bool
  val is_var_or_const : term -> bool 
  
(* quantifier functions *) 
  val strip_quant : term -> (term list * term)
  val bound_by_quant : term -> term -> bool 

  val list_mk_var : (string list * hol_type list) -> term list
  val create_newvar : term -> term list -> term 
  
  val name_of : term -> string
  val name_tff : string -> term -> string
  val name_numeral : term -> string

  val find_atoml : term -> term list 
  val find_predicatel : term -> term list 
  val is_predicate_in : term -> term -> bool
  val find_unpredicatel : term -> term list
(* thm *)
  val rewrite_conv : conv -> thm -> thm 
  val rewrite_conv_hyp : conv -> term -> thm -> thm

end