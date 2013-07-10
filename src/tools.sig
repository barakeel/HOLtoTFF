signature tools =
sig

type term = Term.term
type hol_type = Type.hol_type
type thm = Thm.thm
type conv = Term.term -> Thm.thm

  val find_atoml : term -> term list 
  val find_predicatel : term -> term list 
  val is_predicate_in : term -> term -> bool

(* test functions *) 
  val has_boolty : term -> bool  
  val has_numty : term -> bool
  val is_var_or_const : term -> bool 
(* end test functions *)
 
(* quantifier functions *) 
  val strip_quant : term -> (term list * term)
  val bound_by_quant : term -> term -> bool 
(* end quantifier *) 

(* term *)
  val list_mk_var : (string list * hol_type list) -> term list
(* thm *)
  val rewrite_conv : conv -> thm -> thm 



end