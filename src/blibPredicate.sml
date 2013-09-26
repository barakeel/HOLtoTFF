structure blibPredicate :> blibPredicate =
struct

open HolKernel Abbrev boolLib numSyntax
     blibBtools blibDatatype 
     blibSyntax blibTffsyntax
     
fun PREDICATE_ERR function message =
    HOL_ERR {origin_structure = "blibPredicate",
	           origin_function = function,
             message = message}


fun find_atoml term =
  case termstructure term of
    Comb =>
    (
    case connector term of
      Forall => find_atoml_quant term 
    | Exists => find_atoml_quant term   
    | Conj => find_atoml_binop term 
    | Neg => find_atoml_unop term 
    | Imp_only => find_atoml_binop term
    | Disj => find_atoml_binop term 
    | App => [term]
    )             
  | _ => [term]  
and find_atoml_quant term =
  let val (qbvl,t) = strip_quant term in find_atoml t end  
and find_atoml_binop term =
  find_atoml (lhand term) @ find_atoml (rand term)
and find_atoml_unop term =
  find_atoml (rand term)

fun find_pred_one atom =
  let val (operator,argl) = strip_comb atom in
    [operator]
  end
  
fun find_pred term = 
  let val atoml = find_atoml term in
    erase_double_aconv (List.concat (map find_pred_one atoml))          
  end 

fun is_pred_in var term = 
  is_member_aconv var (find_pred term)

fun find_unpred_arg arg =
  filter is_var_or_const (all_fosubterm arg)

fun find_unpred_aux atom =
  let val (operator,argl) = strip_comb atom in
    erase_double_aconv (List.concat (map (find_unpred_arg) argl))
  end      

fun find_unpred term =
  let val atoml = find_atoml term in
   erase_double_aconv (List.concat (map find_unpred_aux atoml))
  end              

fun has_boolarg term = not (null (filter has_boolty (find_unpred term)))

fun has_boolarg_thm thm =
  let val l = (hyp thm) @ [concl thm] in
    exists has_boolarg l
  end  

fun has_boolarg_goal goal =
  let val l = (fst goal) @ [snd goal] in
    exists has_boolarg l
  end

end