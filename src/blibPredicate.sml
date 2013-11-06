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
  case structterm term of
    Comb =>
    (
    case structcomb term of
      Forall => find_atoml_quant term 
    | Exists => find_atoml_quant term   
    | Conj => find_atoml_binop term 
    | Neg => find_atoml_unop term 
    | Imp_only => find_atoml_binop term
    | Disj => find_atoml_binop term 
    | _ => [term]
    )             
  | _ => [term]  
and find_atoml_quant term =
  let val (qbvl,t) = strip_quant term in find_atoml t end  
and find_atoml_binop term =
  find_atoml (lhand term) @ find_atoml (rand term)
and find_atoml_unop term =
  find_atoml (rand term)

fun find_pred_one atom =  fst (strip_comb atom)

fun find_pred term = 
  let val atoml = find_atoml term in
    erase_double (map find_pred_one atoml)          
  end 

fun is_pred_in var term = 
  is_member_aconv var (find_pred term)

fun has_boolarg_one term =
  let val argl = snd (strip_comb term) in
    exists has_boolty argl orelse
    exists has_boolarg_one argl
  end
           
fun has_boolarg term = 
  let val atoml = find_atoml term in
    exists has_boolarg_one atoml
  end

fun has_boolarg_thm thm =
  let val l = (hyp thm) @ [concl thm] in
    exists has_boolarg l
  end  

fun has_boolarg_goal goal =
  let val l = (fst goal) @ [snd goal] in
    exists has_boolarg l
  end

end