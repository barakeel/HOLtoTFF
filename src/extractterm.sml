structure extractterm :> extractterm =
struct

open HolKernel Abbrev boolLib 
     listtools mydatatype 
     syntax
     
fun EXTRACTTERM_ERR function message =
  HOL_ERR{origin_structure = "extractterm",
          origin_function = function,
          message = message}


fun all_subterm_aux term = 
  case termstructure term of
    Numeral => [term]
  | Var => [term]  
  | Const => [term]
  | Comb => 
    (
    case connector term of
      Forall => all_subterm_aux_quant term
    | Exists => all_subterm_aux_quant term   
    | Conj => all_subterm_aux_binop term
    | Neg => all_subterm_aux_unop term
    | Imp_only => all_subterm_aux_binop term
    | Disj => all_subterm_aux_binop term
    | App => let val (operator,argl) = strip_comb term in
               term :: all_subterm_aux_list (operator :: argl)            
             end
    )  
  | Abs => term :: all_subterm_aux (snd (strip_abs term))
         
and all_subterm_aux_list terml = 
  erase_double_aconv (List.concat (map (all_subterm_aux) terml))
and all_subterm_aux_quant term = all_subterm_aux (snd (strip_quant term))
and all_subterm_aux_binop term = all_subterm_aux_list [lhand term,rand term] 
and all_subterm_aux_unop term = all_subterm_aux (rand term)

fun all_subterm term = erase_double_aconv (all_subterm_aux term)

end