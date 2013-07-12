signature tools =
sig

type term = Term.term
type hol_type = Type.hol_type
type thm = Thm.thm
type conv = Term.term -> Thm.thm

(* test *) 
  val has_boolty : term -> bool  
  val has_numty : term -> bool
  val is_var_or_const : term -> bool 
  
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
  val create_newvar : term -> term list -> term 

(* arity *)
  val get_arity : term -> int
  val collapse_lowestarity : (term * int) list -> (term * int) list  
  
(* conv *)
  val repeat_n_conv : int -> conv -> conv 
  val not_exists_list_conv : conv
  
(* rule *)
  val rewrite_conv : conv -> thm -> thm 
  val rewrite_conv_hyp : conv -> term -> thm -> thm
  val list_prove_hyp : thm list -> thm -> thm 
  val list_conj_hyp : thm -> thm
  val ap_thm_list : thm -> term list -> thm 

(* first order *)  
  val find_atoml : term -> term list 
  val find_predicatel : term -> term list 
  val is_predicate_in : term -> term -> bool
  val find_unpredicatel : term -> term list
  val has_boolarg : term -> bool
  val has_boolarg_thm : thm -> bool
 

end